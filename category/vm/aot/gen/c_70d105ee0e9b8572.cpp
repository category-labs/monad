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

// Written by aotgen.py from the code whose keccak is 70d105ee0e9b857244d87521bbcef34cfb4cbd600592af61bbc7c76180648d61: not to be edited.

#include <category/vm/aot/ops.hpp>
#include <category/vm/interpreter/execute.hpp>
#include <category/vm/interpreter/intercode.hpp>

#define MONAD_AOT_TAIL __attribute__((musttail))

namespace monad::vm::aot
{
    using runtime::Context;
    using runtime::StatusCode;

    // 10137 bytes, keccak 70d105ee0e9b857244d87521bbcef34cfb4cbd600592af61bbc7c76180648d61
    namespace c_70d105ee0e9b8572
    {
        template <Traits traits>
        using Block = void (*)(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        [[gnu::noinline]] void b_0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_26(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_9d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_bf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_eb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_100(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_112(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_118(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_12d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_133(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_151(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_166(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_18e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_200(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_206(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_210(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_226(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_232(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_238(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_243(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_249(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_258(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_25e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_26d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_273(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_285(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_28b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2a0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2a6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2c4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2d9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2f5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_304(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_313(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_326(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_330(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_33f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_390(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3a8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3b0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3f3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_419(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_41f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_42a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_430(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_456(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_497(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4ae(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4c5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4ea(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_50c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_54e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_567(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_59e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_5b2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_5d2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_627(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_655(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_66e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_692(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6a0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6b7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6ce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6e8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6fd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_741(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_755(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_761(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_778(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_79e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_7ac(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_7c3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_7d6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_810(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_815(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_820(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_824(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_853(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_858(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_863(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_867(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_8ab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_8ca(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_8e8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_905(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_921(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_93c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_956(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_970(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_989(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9a1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9b8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9ce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9e3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9f6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a00(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a0d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a1b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a2a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a39(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a49(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a5a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a6c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a7f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a93(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_aa7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_abc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ad2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ae5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b3e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b58(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b6d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_bbd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_bd8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c20(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c6e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c82(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c95(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_caf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_cd6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_cf2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_cff(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d1b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d27(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d39(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d45(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d53(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d5f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d6b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d77(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_de7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_deb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_dfe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e29(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e34(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_e41(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e4e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e75(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_e80(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e8d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_e9a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ea7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_eab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ebe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ecf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_edf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_eec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f13(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f1e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f30(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f43(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f50(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f54(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_fab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_fe3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_fff(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1016(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_103c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_104f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1060(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1077(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10d2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10e4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10f4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_111b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1141(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1147(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1155(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_115b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1160(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1166(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1172(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_117c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1185(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1191(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_119b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11ca(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_11d7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11eb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1247(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_13eb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_13f4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_13fd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1403(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_140f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1419(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_141f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_142c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1432(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_143d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1443(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1452(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1458(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1467(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_146d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1480(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_148c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_149b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_14a1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_14b6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14bc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14e5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14ed(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1503(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1526(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1532(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1544(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1550(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_155e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_156a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1576(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1582(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_15f8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1601(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1636(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1642(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1654(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1660(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_166e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_167a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1686(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1692(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1709(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_170f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1725(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1735(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_174a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_176f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1785(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_17a2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_17b6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_17c7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_17f0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1807(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1820(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1834(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_185f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1889(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1898(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18ae(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18ba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18cb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18ef(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18fe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_191a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_192e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_193c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1961(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_197d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_19aa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_19cd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_19dc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_19e8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a16(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a39(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a48(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a50(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a5e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a71(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a7e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a8b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a9b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1aa8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ae1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ae9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1aee(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b1b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b26(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b43(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1b49(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1b5a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b60(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b6a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1b76(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b81(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1be6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1be8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1bf4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1bfe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c10(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1c16(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1c2b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c31(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c48(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c5d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c8c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1cc3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1cd8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1cf0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d0f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d53(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d62(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1da6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dbe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dcd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e06(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e1e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e2d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e41(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e4e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e71(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1e7c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1e82(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e99(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ea7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1eb3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ec5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ed1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ee3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1eef(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f01(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f0d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f1f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f2b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f3d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f49(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f5b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f67(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f70(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f78(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f7e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f89(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f8f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f98(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1fa0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fc9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fe5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2000(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2015(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_201c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2032(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_203f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_204f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2077(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2168(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2183(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2194(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_21a4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_21ad(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21bd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21c7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21ec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2204(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_220c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2237(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2242(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_226c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2272(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_227d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2283(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_22c3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_22e9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_22fb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2306(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2323(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2340(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2353(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2365(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2374(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_237e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2391(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_23a0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_23a6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_23c6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_23d1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_23ec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_23f9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2414(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2428(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2433(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_245e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_246a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_248b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_24b1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_24cb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_24d9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_24eb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_250a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_251f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2531(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_253d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2550(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_255f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2578(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_25a6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_25b2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_25c0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_25e7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_25f3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2604(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2630(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_263c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_264d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2662(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2674(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2680(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_268f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_26a3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_26b5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_26c1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_26d4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_26dc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2707(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2714(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_271f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2786(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2788(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        void bad(Context *const ctx, uint256_t const *, uint256_t *, int64_t)
        {
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        inline constexpr Block<traits> jump_table[10137] = {
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_9d<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_c5<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_d0<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_eb<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_fa<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_118<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_12d<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_166<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_18e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1f2<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_200<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_210<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_238<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_243<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_25e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_26d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_28b<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2a0<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2d9<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_41f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_42a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_815<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_824<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_858<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_867<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_a00<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_a0d<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_a1b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_a2a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_a39<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_a49<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_a5a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_a6c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_a7f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_a93<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_aa7<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_abc<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_ad2<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_ae5<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_cd6<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_cf2<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_d27<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_d45<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_d5f<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_d77<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_deb<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_e41<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_e80<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_e9a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_eab<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_edf<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_f1e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_f43<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_f54<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1147<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1155<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1160<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1166<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1185<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_11d7<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1247<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_13fd<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1403<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_141f<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1432<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_143d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1458<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1467<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_148c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_14a1<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_14b6<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1532<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1550<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_156a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1582<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1601<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1642<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1660<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_167a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1692<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_170f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1735<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_17b6<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_17c7<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_19e8<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1a50<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1a71<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1a7e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1a9b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1aa8<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1aee<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1b49<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1b5a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1b76<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1be6<traits>, &bad<traits>, &b_1be8<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1c16<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1c2b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1e7c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1e82<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1ea7<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1ec5<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1ee3<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1f01<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1f1f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1f3d<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1f5b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1f70<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1f7e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1f89<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1f98<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1fa0<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2000<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2015<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_201c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2032<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2194<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_21a4<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_21ad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2272<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_227d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_22c3<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_237e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_23a6<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_253d<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2550<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2680<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_268f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_26c1<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_26dc<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2714<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2786<traits>, &bad<traits>, &b_2788<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>,
        };

        template <Traits traits>
        [[gnu::noinline]] void b_0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x60, 0x1c, 0x60, 0x60, 0x82, 0x06, 0x60, 0x1b, 0x61, 0x01, 0x60, 0x39, 0x60, 0x51, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x60, 0x1c, 0x60, 0x60, 0x82, 0x06, 0x60, 0x1b, 0x61, 0x01, 0x60, 0x39, 0x60, 0x51, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x0ull});
            uint256_t const t2 = aot::shr_c<224>(t1);
            uint256_t const t3 = aot::umod(t2, uint256_t{0x6ull});
            uint256_t const t4 = aot::shl_c<1>(t3);
            uint256_t const t5 = uint256_t{0x278dull} + t4;
            uint256_t const k13_0 = uint256_t{0x1eull};
            uint256_t const k13_2 = uint256_t{0x2ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k13_0, &t5, &k13_2);
            gas = ctx->gas_remaining;
            uint256_t const t6 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint64_t const jt = aot::jump_offset(t6);
            top[1] = t2;
            top += 1;
            if (MONAD_LIKELY(jt < 10137)) {
                MONAD_AOT_TAIL return jump_table<traits>[jt](ctx, bottom, top, gas);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0x54fd4d50ull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1e7c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_26<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_26(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x34, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j2 = aot::nonzero(t1);
            if (j2) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0x60, 0x52, 0x60, 0x60, 0x52, 0x7f, 0x60, 0x52, 0x60, 0x81, 0x60, 0x01, 0x81, 0x51, 0x81, 0x52, 0x60, 0x82, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x80, 0x51, 0x80, 0x60, 0x83, 0x01, 0x01, 0x60, 0x82, 0x60, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x60, 0x19, 0x60, 0x82, 0x51, 0x60, 0x01, 0x01, 0x16, 0x90, 0x50, 0x90, 0x50, 0x81, 0x01, 0x90, 0x50, 0x60, 0xf3}, 0, 8));
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0x60, 0x52, 0x60, 0x60, 0x52, 0x7f, 0x60, 0x52, 0x60, 0x81, 0x60, 0x01, 0x81, 0x51, 0x81, 0x52, 0x60, 0x82, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x80, 0x51, 0x80, 0x60, 0x83, 0x01, 0x01, 0x60, 0x82, 0x60, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x60, 0x19, 0x60, 0x82, 0x51, 0x60, 0x01, 0x01, 0x16, 0x90, 0x50, 0x90, 0x50, 0x81, 0x01, 0x90, 0x50, 0x60, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, uint256_t{0x20ull});
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, uint256_t{0x6ull});
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x76322e312e300000ull});
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t2);
            uint256_t const t3 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t4 = uint256_t{0xc0ull} + t3;
            uint256_t const t5 = uint256_t{0x0ull} - t3;
            uint256_t const t6 = t5 & uint256_t{0x1full};
            uint256_t const t7 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t4, &t7, &t6);
            gas = ctx->gas_remaining;
            uint256_t const t8 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t9 = uint256_t{0x20ull} + t8;
            uint256_t const t10 = t9 + uint256_t{0x1full};
            uint256_t const t11 = t10 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t12 = uint256_t{0x20ull} + t11;
            aot::finish(ctx, gas, StatusCode::Success, uint256_t{0x80ull}, t12);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_9d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0x29fcfcf2ull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1e7c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_a9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x34, 0x17, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x34, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xc4ull});
            uint256_t const t3 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t4 = t3 | t2;
            bool const j6 = aot::nonzero(t4);
            if (j6) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xfa0ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_c5<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_bf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_bf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_d0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x60, 0x35, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x60, 0x35, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0x2625a00ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_d0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_d6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x64, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x64, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x2540be400ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_eb<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_e5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_fa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_eb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x60, 0x35, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x60, 0x35, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0x2c2fd72164d8000ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_fa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_100<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_100(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x67, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x67, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x16345785d8a0000ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_118<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_112<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_112(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_12d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_118(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x6d, 0x60, 0x35, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x6d, 0x60, 0x35, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0x38c15b0a00000000ull, 0x314dc6448d93ull, 0x0ull, 0x0ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_12d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_12d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_133<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_133(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x68, 0x61, 0x52, 0x66, 0x60, 0x35, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x68, 0x61, 0x52, 0x66, 0x60, 0x35, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 832u, 864u, 82>(ctx, gas, uint256_t{0x6bc75e2d63100000ull, 0x5ull, 0x0ull, 0x0ull});
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x470de4df820001ull});
            bool const j8 = aot::nonzero(t2);
            if (j8) { MONAD_AOT_TAIL return b_166<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_151<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_151(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x66, 0x61, 0x51, 0x02, 0x04, 0x61, 0x52}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x66, 0x61, 0x51, 0x02, 0x04, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0x470de4df820000ull});
            uint256_t const t4 = aot::udiv(t3, t1);
            aot::mstore_c<traits, 832u, 864u, 82>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_166<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_166(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x60, 0x37, 0x60, 0x60, 0x60, 0x37, 0x60, 0x60, 0x60, 0x37, 0x61, 0x51, 0x61, 0x52, 0x61, 0x61, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x60, 0x37, 0x60, 0x60, 0x60, 0x37, 0x60, 0x60, 0x60, 0x37, 0x61, 0x51, 0x61, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const k4_0 = uint256_t{0x40ull};
            uint256_t const k4_1 = uint256_t{0x4ull};
            uint256_t const k4_2 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k4_0, &k4_1, &k4_2);
            gas = ctx->gas_remaining;
            uint256_t const k8_0 = uint256_t{0x80ull};
            uint256_t const k8_1 = uint256_t{0x44ull};
            uint256_t const k8_2 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k8_0, &k8_1, &k8_2);
            gas = ctx->gas_remaining;
            uint256_t const k12_0 = uint256_t{0xc0ull};
            uint256_t const k12_1 = uint256_t{0x84ull};
            uint256_t const k12_2 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k12_0, &k12_1, &k12_2);
            gas = ctx->gas_remaining;
            uint256_t const t1 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            aot::mstore_c<traits, 256u, 288u, 27>(ctx, gas, t1);
            top[1] = uint256_t{0x18eull};
            top[2] = uint256_t{0x380ull};
            top += 2;
            MONAD_AOT_TAIL return b_21ad<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_18e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
            aot::mstore_c<traits, 864u, 896u, 85>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 864u, 896u, 85>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = aot::udiv(t3, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t5 = t4 ^ t2;
            bool const j16 = aot::nonzero(t5);
            top[1] = t2;
            top[2] = t3;
            top += 2;
            if (j16) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1b7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x35, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x35, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1c2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x6e, 0x04, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x6e, 0x04, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 896u, 928u, 88>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t3 = aot::udiv(uint256_t{0xd9a5cf8800000000ull, 0x604be73de4838aull, 0x0ull, 0x0ull}, t2);
            uint256_t const t4 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
            uint256_t const t5 = aot::from_bool(t4 < t3);
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j18 = aot::nonzero(t6);
            top += -2;
            if (j18) { MONAD_AOT_TAIL return b_1f2<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1ec<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_200<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x60, 0x1c, 0x61, 0x51, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x60, 0x1c, 0x61, 0x51, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t2 = aot::shr_c<1>(t1);
            uint256_t const t3 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
            uint256_t const t4 = aot::from_bool(t2 < t3);
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            top[1] = t5;
            top += 1;
            MONAD_AOT_TAIL return b_200<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_200(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_206<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_206(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0xf3}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Success, uint256_t{0x360ull}, uint256_t{0x20ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_210(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0x43d188fbull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1e7c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_21c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x34, 0x17, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x34, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xc4ull});
            uint256_t const t3 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t4 = t3 | t2;
            bool const j6 = aot::nonzero(t4);
            if (j6) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_226<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_226(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xfa0ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_238<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_232<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_232(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_243<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_238(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x60, 0x35, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x60, 0x35, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0x2625a00ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_243<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_243(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_249<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_249(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x64, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x64, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x2540be400ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_25e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_258<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_258(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_26d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_25e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x60, 0x35, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x60, 0x35, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0x2c2fd72164d8000ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_26d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_26d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_273<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_273(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x67, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x67, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x16345785d8a0000ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_28b<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_285<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_285(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_2a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_28b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x6d, 0x60, 0x35, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x6d, 0x60, 0x35, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0x38c15b0a00000000ull, 0x314dc6448d93ull, 0x0ull, 0x0ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_2a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2a0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2a6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2a6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x68, 0x61, 0x52, 0x66, 0x60, 0x35, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x68, 0x61, 0x52, 0x66, 0x60, 0x35, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 832u, 864u, 82>(ctx, gas, uint256_t{0x6bc75e2d63100000ull, 0x5ull, 0x0ull, 0x0ull});
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x470de4df820001ull});
            bool const j8 = aot::nonzero(t2);
            if (j8) { MONAD_AOT_TAIL return b_2d9<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2c4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2c4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x66, 0x61, 0x51, 0x02, 0x04, 0x61, 0x52}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x66, 0x61, 0x51, 0x02, 0x04, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0x470de4df820000ull});
            uint256_t const t4 = aot::udiv(t3, t1);
            aot::mstore_c<traits, 832u, 864u, 82>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_2d9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2d9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2e6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x60, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x60, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 864u, 896u, 85>(ctx, gas, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j8 = aot::nonzero(t2);
            top[0] = t1;
            if (j8) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2f5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2f5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x60, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x60, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 896u, 928u, 88>(ctx, gas, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j8 = aot::nonzero(t2);
            top[0] = t1;
            if (j8) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_304<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_304(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x60, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x60, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 928u, 960u, 91>(ctx, gas, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j8 = aot::nonzero(t2);
            top[0] = t1;
            if (j8) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_313<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_313(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x60, 0x35, 0x80, 0x60, 0x03, 0x60, 0x81, 0x11, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x60, 0x35, 0x80, 0x60, 0x03, 0x60, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 960u, 992u, 94>(ctx, gas, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const t2 = uint256_t{0x1ull} - t1;
            uint256_t const t3 = aot::from_bool(uint256_t{0x1ull} < t2);
            bool const j11 = aot::nonzero(t3);
            top[0] = t1;
            top[1] = t2;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_326<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_326(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x81, 0x11, 0x61, 0x57}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x1ull} < s0);
            bool const j6 = aot::nonzero(t1);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (j6) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_330<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_330(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1b, 0x60, 0x01, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1b, 0x60, 0x01, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const t2 = uint256_t{0x44ull} + t1;
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const t4 = aot::shr_c<255>(t3);
            bool const j9 = aot::nonzero(t4);
            top[0] = t3;
            if (j9) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_33f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_33f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x02, 0x61, 0x52, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x02, 0x61, 0x52, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 992u, 1024u, 98>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 928u, 960u, 91>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 928u, 960u, 91>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, t1);
            aot::mstore_c<traits, 1024u, 1056u, 101>(ctx, gas, t3);
            uint256_t const t4 = aot::mload_c<traits, 960u, 992u, 94>(ctx, gas);
            uint256_t const t5 = aot::from_bool(slt(t4, uint256_t{0x597d89b3754abea0ull, 0xb504f333f9de6484ull, 0x0ull, 0x0ull}));
            uint256_t const t6 = aot::from_bool(slt(uint256_t{0xa682764c8ab54160ull, 0x4afb0ccc06219b7bull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t4));
            uint256_t const t7 = t6 & t5;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j20 = aot::nonzero(t8);
            top[0] = t4;
            if (j20) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_390<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_390(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x61, 0x51, 0x80, 0x60, 0x1b, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x61, 0x51, 0x80, 0x60, 0x1b, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::exp_c<0x2u>(s0);
            uint256_t const t2 = aot::mload_c<traits, 992u, 1024u, 98>(ctx, gas);
            uint256_t const t3 = aot::shl_c<2>(t2);
            uint256_t const k13_1 = uint256_t{0x4ull};
            uint256_t r13;
            runtime::sdiv(&r13, &t3, &k13_1);
            uint256_t const t4 = r13 ^ t2;
            bool const j16 = aot::nonzero(t4);
            top[0] = t1;
            top[1] = t2;
            top[2] = t3;
            top += 2;
            if (j16) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3a8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3a8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x80, 0x15, 0x61, 0x57}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j5 = aot::nonzero(t1);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (j5) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3b0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3b0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t r2;
            runtime::sdiv(&r2, &s1, &s0);
            uint256_t const t1 = aot::from_bool(s1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(s0 == uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = t4 | t2;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j17 = aot::nonzero(t6);
            top[1] = r2;
            top += 1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3c7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x05, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x05, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1056u, 1088u, 104>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 960u, 992u, 94>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 992u, 1024u, 98>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0x1bc16d674ec80000ull});
            uint256_t const k16_1 = uint256_t{0x1bc16d674ec80000ull};
            uint256_t r16;
            runtime::sdiv(&r16, &t3, &k16_1);
            uint256_t const t4 = r16 ^ t2;
            bool const j19 = aot::nonzero(t4);
            top[-2] = t1;
            top[-1] = t2;
            top[0] = t3;
            if (j19) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3f3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3f3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x6e, 0x05, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x6e, 0x05, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t r2;
            runtime::sdiv(&r2, &s0, &s2);
            aot::mstore_c<traits, 1088u, 1120u, 107>(ctx, gas, r2);
            uint256_t const t1 = aot::mload_c<traits, 864u, 896u, 85>(ctx, gas);
            uint256_t const k8_0 = uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull};
            uint256_t r8;
            runtime::sdiv(&r8, &k8_0, &t1);
            uint256_t const t2 = aot::mload_c<traits, 1088u, 1120u, 107>(ctx, gas);
            uint256_t const t3 = aot::from_bool(slt(t2, r8));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j14 = aot::nonzero(t4);
            top += -3;
            if (j14) { MONAD_AOT_TAIL return b_41f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_419<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_419(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_42a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_41f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x13, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x13, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 864u, 896u, 85>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1088u, 1120u, 107>(ctx, gas);
            uint256_t const t3 = aot::from_bool(slt(t1, t2));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            top[1] = t4;
            top += 1;
            MONAD_AOT_TAIL return b_42a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_42a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_430<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_430(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 0, 8));
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1024u, 1056u, 101>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = ~t2;
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const t7 = aot::from_bool(t1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            uint256_t const t9 = t8 | t6;
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t2));
            uint256_t r23;
            runtime::sdiv(&r23, &t3, &t2);
            uint256_t const t11 = aot::from_bool(r23 == t1);
            uint256_t const t12 = t11 | t10;
            uint256_t const t13 = t12 & t9;
            uint256_t const t14 = aot::from_bool(!aot::nonzero(t13));
            bool const j29 = aot::nonzero(t14);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j29) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_456<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_456(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x6d, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x6d, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1120u, 1152u, 110>(ctx, gas, s0);
            aot::mstore_c<traits, 1152u, 1184u, 113>(ctx, gas, uint256_t{0x85acef8100000000ull, 0x4ee2d6d415bull, 0x0ull, 0x0ull});
            uint256_t const t1 = aot::mload_c<traits, 960u, 992u, 94>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1120u, 1152u, 110>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = ~t2;
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const t7 = aot::from_bool(t1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            uint256_t const t9 = t8 | t6;
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t2));
            uint256_t r32;
            runtime::sdiv(&r32, &t3, &t2);
            uint256_t const t11 = aot::from_bool(r32 == t1);
            uint256_t const t12 = t11 | t10;
            uint256_t const t13 = t12 & t9;
            uint256_t const t14 = aot::from_bool(!aot::nonzero(t13));
            bool const j38 = aot::nonzero(t14);
            top[-2] = t1;
            top[-1] = t2;
            top[0] = t3;
            if (j38) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_497<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_497(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x63, 0x81, 0x05, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x63, 0x81, 0x05, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const k6_1 = uint256_t{0x17d78400ull};
            uint256_t r6;
            runtime::sdiv(&r6, &s0, &k6_1);
            uint256_t const t1 = aot::mload_c<traits, 992u, 1024u, 98>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j14 = aot::nonzero(t2);
            top[-2] = r6;
            top[-1] = t1;
            top += -1;
            if (j14) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_4ae<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4ae(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t r2;
            runtime::sdiv(&r2, &s1, &s0);
            uint256_t const t1 = aot::from_bool(s1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(s0 == uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = t4 | t2;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j17 = aot::nonzero(t6);
            top[1] = r2;
            top += 1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_4c5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4c5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x6d, 0x60, 0x0b, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x6d, 0x60, 0x0b, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = signextend(uint256_t{0xdull}, uint256_t{0x9106ce8300000000ull, 0xeca8847c412ull, 0x0ull, 0x0ull});
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 - t1;
            uint256_t const t3 = aot::from_bool(slt(s0, t2));
            uint256_t const t4 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            uint256_t const t5 = t4 ^ t3;
            bool const j18 = aot::nonzero(t5);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = t2;
            if (j18) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_4ea<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4ea(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x65, 0x61, 0x51, 0x60, 0x1b, 0x02, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x65, 0x61, 0x51, 0x60, 0x1b, 0x02, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 928u, 960u, 91>(ctx, gas);
            uint256_t const t2 = aot::shl_c<1>(t1);
            uint256_t const t3 = aot::mul(t2, uint256_t{0x5af3107a4000ull});
            uint256_t const &s0 = top[0];
            uint256_t const t4 = s0 - t3;
            uint256_t const t5 = aot::from_bool(slt(s0, t4));
            uint256_t const t6 = aot::from_bool(slt(t3, uint256_t{0x0ull}));
            uint256_t const t7 = t6 ^ t5;
            bool const j21 = aot::nonzero(t7);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t3;
            top[0] = t4;
            if (j21) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_50c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_50c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x65, 0x61, 0x51, 0x60, 0x1b, 0x02, 0x80, 0x6d, 0x01, 0x6d, 0x81, 0x12, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x65, 0x61, 0x51, 0x60, 0x1b, 0x02, 0x80, 0x6d, 0x01, 0x6d, 0x81, 0x12, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1184u, 1216u, 116>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 928u, 960u, 91>(ctx, gas);
            uint256_t const t2 = aot::shl_c<2>(t1);
            uint256_t const t3 = aot::mul(t2, uint256_t{0x5af3107a4000ull});
            uint256_t const t4 = uint256_t{0x9106ce8300000000ull, 0xeca8847c412ull, 0x0ull, 0x0ull} + t3;
            uint256_t const t5 = aot::from_bool(slt(t4, uint256_t{0x9106ce8300000000ull, 0xeca8847c412ull, 0x0ull, 0x0ull}));
            uint256_t const t6 = aot::from_bool(slt(t3, uint256_t{0x0ull}));
            uint256_t const t7 = t6 ^ t5;
            bool const j23 = aot::nonzero(t7);
            top[-2] = t3;
            top[-1] = t4;
            top += -1;
            if (j23) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_54e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_54e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x61, 0x51, 0x05, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x61, 0x51, 0x05, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1024u, 1056u, 101>(ctx, gas);
            uint256_t const k5_1 = uint256_t{0x2710ull};
            uint256_t r5;
            runtime::sdiv(&r5, &t1, &k5_1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 + r5;
            uint256_t const t3 = aot::from_bool(slt(t2, s0));
            uint256_t const t4 = aot::from_bool(slt(r5, uint256_t{0x0ull}));
            uint256_t const t5 = t4 ^ t3;
            bool const j17 = aot::nonzero(t5);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = r5;
            top[1] = t2;
            top += 1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_567<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_567(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x63, 0x61, 0x51, 0x60, 0x1b, 0x05, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 3, 7));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x63, 0x61, 0x51, 0x60, 0x1b, 0x05, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 960u, 992u, 94>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1120u, 1152u, 110>(ctx, gas);
            uint256_t const t3 = aot::shl_c<2>(t2);
            uint256_t const k11_1 = uint256_t{0x17d78400ull};
            uint256_t r11;
            runtime::sdiv(&r11, &t3, &k11_1);
            uint256_t const t4 = aot::mload_c<traits, 992u, 1024u, 98>(ctx, gas);
            uint256_t const t5 = aot::mul(r11, t4);
            uint256_t const t6 = ~t4;
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            uint256_t const t9 = aot::from_bool(r11 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            uint256_t const t11 = t10 | t8;
            uint256_t const t12 = aot::from_bool(!aot::nonzero(t4));
            uint256_t r33;
            runtime::sdiv(&r33, &t5, &t4);
            uint256_t const t13 = aot::from_bool(r33 == r11);
            uint256_t const t14 = t13 | t12;
            uint256_t const t15 = t14 & t11;
            uint256_t const t16 = aot::from_bool(!aot::nonzero(t15));
            bool const j39 = aot::nonzero(t16);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = r11;
            top[1] = t4;
            top[2] = t5;
            top += 2;
            if (j39) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_59e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_59e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 5, 1));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s4 + r4;
            uint256_t const t2 = aot::from_bool(slt(t1, s4));
            uint256_t const t3 = aot::from_bool(slt(r4, uint256_t{0x0ull}));
            uint256_t const t4 = t3 ^ t2;
            bool const j16 = aot::nonzero(t4);
            top[-3] = r4;
            top[-2] = t1;
            top += -2;
            if (j16) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_5b2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_5b2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x63, 0x61, 0x51, 0x60, 0x1b, 0x05, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x63, 0x61, 0x51, 0x60, 0x1b, 0x05, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1120u, 1152u, 110>(ctx, gas);
            uint256_t const t2 = aot::shl_c<2>(t1);
            uint256_t const k9_1 = uint256_t{0x17d78400ull};
            uint256_t r9;
            runtime::sdiv(&r9, &t2, &k9_1);
            uint256_t const &s0 = top[0];
            uint256_t const t3 = s0 - r9;
            uint256_t const t4 = aot::from_bool(slt(s0, t3));
            uint256_t const t5 = aot::from_bool(slt(r9, uint256_t{0x0ull}));
            uint256_t const t6 = t5 ^ t4;
            bool const j21 = aot::nonzero(t6);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = r9;
            top[0] = t3;
            if (j21) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_5d2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_5d2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x61, 0x51, 0x67, 0x01, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x61, 0x51, 0x67, 0x01, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1216u, 1248u, 119>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 928u, 960u, 91>(ctx, gas);
            uint256_t const t2 = uint256_t{0xde0b6b3a7640000ull} + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x597d89b3754abea0ull, 0xb504f333f9de6484ull, 0x0ull, 0x0ull}));
            uint256_t const t4 = aot::from_bool(slt(uint256_t{0xa682764c8ab54160ull, 0x4afb0ccc06219b7bull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t2));
            uint256_t const t5 = t4 & t3;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j20 = aot::nonzero(t6);
            top[-2] = uint256_t{0x2710ull};
            top[-1] = t2;
            top += -1;
            if (j20) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_627<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_627(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x05, 0x7f, 0x81, 0x14, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x05, 0x7f, 0x81, 0x14, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::exp_c<0x2u>(s0);
            uint256_t const &s1 = top[-1];
            uint256_t r5;
            runtime::sdiv(&r5, &t1, &s1);
            uint256_t const t2 = aot::from_bool(r5 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            bool const j10 = aot::nonzero(t2);
            top[-1] = r5;
            top += -1;
            if (j10) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_655<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_655(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x03, 0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x03, 0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            aot::mstore_c<traits, 1248u, 1280u, 123>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 1152u, 1184u, 113>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0x3ull});
            uint256_t const k12_1 = uint256_t{0x3ull};
            uint256_t r12;
            runtime::sdiv(&r12, &t3, &k12_1);
            uint256_t const t4 = r12 ^ t2;
            bool const j15 = aot::nonzero(t4);
            top[0] = t2;
            top[1] = t3;
            top += 1;
            if (j15) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_66e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_66e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1216u, 1248u, 119>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::mul(s0, t1);
            uint256_t const t3 = ~t1;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(s0 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t1));
            uint256_t r23;
            runtime::sdiv(&r23, &t2, &t1);
            uint256_t const t10 = aot::from_bool(r23 == s0);
            uint256_t const t11 = t10 | t9;
            uint256_t const t12 = t11 & t8;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t12));
            bool const j29 = aot::nonzero(t13);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            top[1] = t2;
            top += 1;
            if (j29) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_692<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_692(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_6a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6a0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t r2;
            runtime::sdiv(&r2, &s1, &s0);
            uint256_t const t1 = aot::from_bool(s1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(s0 == uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = t4 | t2;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j17 = aot::nonzero(t6);
            top[1] = r2;
            top += 1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_6b7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6b7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 - t1;
            uint256_t const t3 = aot::from_bool(slt(s0, t2));
            uint256_t const t4 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            uint256_t const t5 = t4 ^ t3;
            bool const j17 = aot::nonzero(t5);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = t2;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_6ce<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6ce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1280u, 1312u, 126>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1280u, 1312u, 126>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0x3ull});
            uint256_t const k14_1 = uint256_t{0x3ull};
            uint256_t r14;
            runtime::sdiv(&r14, &t2, &k14_1);
            uint256_t const t3 = r14 ^ t1;
            bool const j17 = aot::nonzero(t3);
            top[-2] = t1;
            top[-1] = t2;
            top += -1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_6e8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6e8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, s0));
            uint256_t const t4 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            uint256_t const t5 = t4 ^ t3;
            bool const j15 = aot::nonzero(t5);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            top[1] = t2;
            top += 1;
            if (j15) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_6fd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6fd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1152u, 1184u, 113>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x597d89b3754abea0ull, 0xb504f333f9de6484ull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(slt(uint256_t{0xa682764c8ab54160ull, 0x4afb0ccc06219b7bull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t1));
            uint256_t const t4 = t3 & t2;
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            bool const j15 = aot::nonzero(t5);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j15) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_741<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_741(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::exp_c<0x2u>(s0);
            uint256_t const t2 = aot::mul(t1, uint256_t{0x1bull});
            uint256_t const k11_1 = uint256_t{0x1bull};
            uint256_t r11;
            runtime::sdiv(&r11, &t2, &k11_1);
            uint256_t const t3 = r11 ^ t1;
            bool const j14 = aot::nonzero(t3);
            top[0] = t1;
            top[1] = t2;
            top += 1;
            if (j14) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_755<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_755(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_761<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_761(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t r2;
            runtime::sdiv(&r2, &s1, &s0);
            uint256_t const t1 = aot::from_bool(s1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(s0 == uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = t4 | t2;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j17 = aot::nonzero(t6);
            top[1] = r2;
            top += 1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_778<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_778(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1248u, 1280u, 123>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::mul(s0, t1);
            uint256_t const t3 = ~t1;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(s0 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t1));
            uint256_t r25;
            runtime::sdiv(&r25, &t2, &t1);
            uint256_t const t10 = aot::from_bool(r25 == s0);
            uint256_t const t11 = t10 | t9;
            uint256_t const t12 = t11 & t8;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t12));
            bool const j31 = aot::nonzero(t13);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = t2;
            if (j31) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_79e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_79e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_7ac<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_7ac(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t r2;
            runtime::sdiv(&r2, &s1, &s0);
            uint256_t const t1 = aot::from_bool(s1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(s0 == uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = t4 | t2;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j17 = aot::nonzero(t6);
            top[1] = r2;
            top += 1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_7c3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_7c3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s3 - s0;
            uint256_t const t2 = aot::from_bool(slt(s3, t1));
            uint256_t const t3 = aot::from_bool(slt(s0, uint256_t{0x0ull}));
            uint256_t const t4 = t3 ^ t2;
            bool const j15 = aot::nonzero(t4);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j15) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_7d6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_7d6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x61, 0x52, 0x61, 0x51, 0x7f, 0x81, 0x13, 0x15, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x61, 0x52, 0x61, 0x51, 0x7f, 0x81, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1312u, 1344u, 129>(ctx, gas, s0);
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0x1ull});
            uint256_t const t1 = aot::mload_c<traits, 1280u, 1312u, 126>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j16 = aot::nonzero(t3);
            top[-2] = t1;
            top += -2;
            if (j16) { MONAD_AOT_TAIL return b_815<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_810<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_810(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_824<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_815(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x60, 0x03, 0x81, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x60, 0x03, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            uint256_t const t2 = aot::from_bool(s0 == t1);
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_820<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_820(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x60, 0x03}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x60, 0x03}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_824<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_824(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x61, 0x51, 0x7f, 0x81, 0x13, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x61, 0x51, 0x7f, 0x81, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1312u, 1344u, 129>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j10 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j10) { MONAD_AOT_TAIL return b_858<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_853<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_853(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_867<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_858(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x60, 0x03, 0x81, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x60, 0x03, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            uint256_t const t2 = aot::from_bool(s0 == t1);
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_863<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_863(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x60, 0x03}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x60, 0x03}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_867<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_867(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x12, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x12, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x73, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x12, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x12, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x73, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s0 ^ s2;
            uint256_t const t2 = aot::from_bool(slt(s2, s0));
            uint256_t const t3 = aot::mul(t2, t1);
            uint256_t const t4 = t3 ^ s0;
            uint256_t const t5 = aot::mload_c<traits, 1152u, 1184u, 113>(ctx, gas);
            uint256_t const t6 = t5 ^ t4;
            uint256_t const t7 = aot::from_bool(slt(t4, t5));
            uint256_t const t8 = aot::mul(t7, t6);
            uint256_t const t9 = t8 ^ t5;
            aot::mstore_c<traits, 1376u, 1408u, 135>(ctx, gas, t9);
            uint256_t const t10 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t11 = aot::from_bool(slt(t10, uint256_t{0x7f41000000000001ull, 0xe4395d69670b12bull, 0xaf298d05ull, 0x0ull}));
            uint256_t const t12 = aot::from_bool(!aot::nonzero(t11));
            bool const j39 = aot::nonzero(t12);
            top += -3;
            if (j39) { MONAD_AOT_TAIL return b_ad2<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_8ab<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_8ab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x73, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x73, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x6f5a400000000001ull, 0xc5433c60ddaa1640ull, 0x1c06a5eull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_abc<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_8ca<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_8ca(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x72, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x72, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x11d100000000001ull, 0x9673df52e37f2410ull, 0x47bf1ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_aa7<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_8e8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_8e8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x71, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x71, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0xa3d9e40000000001ull, 0xbc627050305adf14ull, 0xb7aull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_a93<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_905<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_905(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x70, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x70, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0xb9f5610000000001ull, 0x6329f1c35ca4bfabull, 0x1dull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_a7f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_921<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_921(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x6f, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x6f, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x98a224000000001ull, 0x4b3b4ca85a86c47aull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_a6c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_93c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_93c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x6e, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x6e, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0xb34b9f1000000001ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_a5a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_956<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_956(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x6e, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x6e, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x378d8e6400000001ull, 0x1ed09bead87c0ull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_a49<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_970<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_970(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x6d, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x6d, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x85acef8100000001ull, 0x4ee2d6d415bull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_a39<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_989<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_989(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x6c, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x6c, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x4674edea40000001ull, 0xc9f2c9cd0ull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_a2a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_9a1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9a1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x6b, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x6b, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x3e25026110000001ull, 0x204fce5eull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_a1b<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_9b8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9b8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x6a, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x6a, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0xdcc80cd2e4000001ull, 0x52b7d2ull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_a0d<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_9ce<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9ce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x69, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x69, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x1bcecceda1000001ull, 0xd3c2ull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_a00<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_9e3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9e3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x68, 0x61, 0x51, 0x12, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x68, 0x61, 0x51, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x6bc75e2d63100001ull, 0x5ull, 0x0ull, 0x0ull}));
            bool const j5 = aot::nonzero(t2);
            if (j5) { MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_9f6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9f6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0x64ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a00(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x62, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x62, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0xf4240ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a0d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0x5f5e100ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a1b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x64, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x64, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0x2540be400ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a2a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x64, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x64, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0xe8d4a51000ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a39(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x65, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x65, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0x5af3107a4000ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a49(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x66, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x66, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0x2386f26fc10000ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a5a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0xde0b6b3a7640000ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a6c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x68, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x68, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0x6bc75e2d63100000ull, 0x5ull, 0x0ull, 0x0ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a7f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x69, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x69, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0x19e0c9bab2400000ull, 0x21eull, 0x0ull, 0x0ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a93(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x69, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x69, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0x1bcecceda1000000ull, 0xd3c2ull, 0x0ull, 0x0ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_aa7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x6a, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x6a, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0xdcc80cd2e4000000ull, 0x52b7d2ull, 0x0ull, 0x0ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_abc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x6b, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x6b, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0x3e25026110000000ull, 0x204fce5eull, 0x0ull, 0x0ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ad2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x6c, 0x61, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x6c, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0x4674edea40000000ull, 0xc9f2c9cd0ull, 0x0ull, 0x0ull});
            MONAD_AOT_TAIL return b_ae5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ae5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x60, 0x02, 0x02, 0x05, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 0, 6));
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x60, 0x02, 0x02, 0x05, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1344u, 1376u, 132>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1152u, 1184u, 113>(ctx, gas);
            uint256_t r5;
            runtime::sdiv(&r5, &t2, &t1);
            aot::mstore_c<traits, 1152u, 1184u, 113>(ctx, gas, r5);
            uint256_t const t3 = aot::mload_c<traits, 1344u, 1376u, 132>(ctx, gas);
            uint256_t const t4 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t r12;
            runtime::sdiv(&r12, &t4, &t3);
            aot::mstore_c<traits, 1184u, 1216u, 116>(ctx, gas, r12);
            uint256_t const t5 = aot::mload_c<traits, 1344u, 1376u, 132>(ctx, gas);
            uint256_t const t6 = aot::mload_c<traits, 1216u, 1248u, 119>(ctx, gas);
            uint256_t r19;
            runtime::sdiv(&r19, &t6, &t5);
            aot::mstore_c<traits, 1216u, 1248u, 119>(ctx, gas, r19);
            uint256_t const t7 = aot::mload_c<traits, 1344u, 1376u, 132>(ctx, gas);
            uint256_t const t8 = aot::mload_c<traits, 1248u, 1280u, 123>(ctx, gas);
            uint256_t r26;
            runtime::sdiv(&r26, &t8, &t7);
            aot::mstore_c<traits, 1248u, 1280u, 123>(ctx, gas, r26);
            uint256_t const t9 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t10 = aot::mload_c<traits, 1216u, 1248u, 119>(ctx, gas);
            uint256_t const t11 = aot::mload_c<traits, 1152u, 1184u, 113>(ctx, gas);
            uint256_t const t12 = aot::mul(uint256_t{0x3ull}, t11);
            uint256_t const t13 = aot::mul(t12, t10);
            uint256_t r38;
            runtime::sdiv(&r38, &t13, &t9);
            uint256_t const t14 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t15 = r38 - t14;
            uint256_t const t16 = aot::from_bool(slt(r38, t15));
            uint256_t const t17 = aot::from_bool(slt(t14, uint256_t{0x0ull}));
            uint256_t const t18 = t17 ^ t16;
            bool const j52 = aot::nonzero(t18);
            top[1] = r38;
            top[2] = t14;
            top[3] = t15;
            top += 3;
            if (j52) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_b3e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b3e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1280u, 1312u, 126>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1280u, 1312u, 126>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0x3ull});
            uint256_t const k14_1 = uint256_t{0x3ull};
            uint256_t r14;
            runtime::sdiv(&r14, &t2, &k14_1);
            uint256_t const t3 = r14 ^ t1;
            bool const j17 = aot::nonzero(t3);
            top[-2] = t1;
            top[-1] = t2;
            top += -1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_b58<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b58(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, s0));
            uint256_t const t4 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            uint256_t const t5 = t4 ^ t3;
            bool const j15 = aot::nonzero(t5);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            top[1] = t2;
            top += 1;
            if (j15) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_b6d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b6d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1248u, 1280u, 123>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t4 = aot::mload_c<traits, 1152u, 1184u, 113>(ctx, gas);
            uint256_t const t5 = aot::from_bool(slt(t4, uint256_t{0x597d89b3754abea0ull, 0xb504f333f9de6484ull, 0x0ull, 0x0ull}));
            uint256_t const t6 = aot::from_bool(slt(uint256_t{0xa682764c8ab54160ull, 0x4afb0ccc06219b7bull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t4));
            uint256_t const t7 = t6 & t5;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j21 = aot::nonzero(t8);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = t2;
            top[1] = t3;
            top[2] = t4;
            top += 2;
            if (j21) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_bbd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_bbd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x60, 0x02, 0x05, 0x02, 0x05, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x60, 0x02, 0x05, 0x02, 0x05, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::exp_c<0x2u>(s0);
            uint256_t const t2 = aot::mul(uint256_t{0x1bull}, t1);
            uint256_t const &s1 = top[-1];
            uint256_t r7;
            runtime::sdiv(&r7, &t2, &s1);
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = aot::mul(r7, s2);
            uint256_t const &s3 = top[-3];
            uint256_t r9;
            runtime::sdiv(&r9, &t3, &s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t4 = s4 - r9;
            uint256_t const t5 = aot::from_bool(slt(s4, t4));
            uint256_t const t6 = aot::from_bool(slt(r9, uint256_t{0x0ull}));
            uint256_t const t7 = t6 ^ t5;
            bool const j21 = aot::nonzero(t7);
            top[-3] = r9;
            top[-2] = t4;
            top += -2;
            if (j21) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_bd8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_bd8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1312u, 1344u, 129>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1312u, 1344u, 129>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x597d89b3754abea0ull, 0xb504f333f9de6484ull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(slt(uint256_t{0xa682764c8ab54160ull, 0x4afb0ccc06219b7bull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t1));
            uint256_t const t4 = t3 & t2;
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            bool const j17 = aot::nonzero(t5);
            top[-2] = t1;
            top += -2;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_c20<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c20(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}, 1, 6));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::exp_c<0x2u>(s0);
            uint256_t const t2 = aot::mload_c<traits, 1280u, 1312u, 126>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t4 = aot::mload_c<traits, 1280u, 1312u, 126>(ctx, gas);
            uint256_t const t5 = aot::from_bool(slt(t4, uint256_t{0x597d89b3754abea0ull, 0xb504f333f9de6484ull, 0x0ull, 0x0ull}));
            uint256_t const t6 = aot::from_bool(slt(uint256_t{0xa682764c8ab54160ull, 0x4afb0ccc06219b7bull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t4));
            uint256_t const t7 = t6 & t5;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j20 = aot::nonzero(t8);
            top[0] = t1;
            top[1] = t2;
            top[2] = t3;
            top[3] = t4;
            top += 3;
            if (j20) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_c6e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c6e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x80, 0x60, 0x1b, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x80, 0x60, 0x1b, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::exp_c<0x2u>(s0);
            uint256_t const t2 = aot::shl_c<2>(t1);
            uint256_t const k11_1 = uint256_t{0x4ull};
            uint256_t r11;
            runtime::sdiv(&r11, &t2, &k11_1);
            uint256_t const t3 = r11 ^ t1;
            bool const j14 = aot::nonzero(t3);
            top[0] = t1;
            top[1] = t2;
            top += 1;
            if (j14) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_c82<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c82(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x05, 0x02, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 5, 1));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x05, 0x02, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t r2;
            runtime::sdiv(&r2, &s0, &s2);
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::mul(r2, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = s4 + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, s4));
            uint256_t const t4 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            uint256_t const t5 = t4 ^ t3;
            bool const j15 = aot::nonzero(t5);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j15) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_c95<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c95(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1408u, 1440u, 138>(ctx, gas, s0);
            aot::mstore_c<traits, 1440u, 1472u, 142>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t1 = aot::mload_c<traits, 1408u, 1440u, 138>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x1ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j15 = aot::nonzero(t3);
            top += -3;
            if (j15) { MONAD_AOT_TAIL return b_cf2<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_caf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_caf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x60, 0x37, 0x60, 0x60, 0x60, 0x37, 0x60, 0x60, 0x60, 0x37, 0x61, 0x51, 0x61, 0x52, 0x61, 0x61, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x60, 0x37, 0x60, 0x60, 0x60, 0x37, 0x60, 0x60, 0x60, 0x37, 0x61, 0x51, 0x61, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const k3_0 = uint256_t{0x40ull};
            uint256_t const k3_1 = uint256_t{0x4ull};
            uint256_t const k3_2 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k3_0, &k3_1, &k3_2);
            gas = ctx->gas_remaining;
            uint256_t const k7_0 = uint256_t{0x80ull};
            uint256_t const k7_1 = uint256_t{0x44ull};
            uint256_t const k7_2 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k7_0, &k7_1, &k7_2);
            gas = ctx->gas_remaining;
            uint256_t const k11_0 = uint256_t{0xc0ull};
            uint256_t const k11_1 = uint256_t{0x84ull};
            uint256_t const k11_2 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k11_0, &k11_1, &k11_2);
            gas = ctx->gas_remaining;
            uint256_t const t1 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            aot::mstore_c<traits, 256u, 288u, 27>(ctx, gas, t1);
            top[1] = uint256_t{0xcd6ull};
            top[2] = uint256_t{0x5c0ull};
            top += 2;
            MONAD_AOT_TAIL return b_21ad<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_cd6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x61, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1472u, 1504u, 145>(ctx, gas);
            aot::mstore_c<traits, 1504u, 1536u, 148>(ctx, gas, t1);
            aot::mstore_c<traits, 1536u, 1568u, 151>(ctx, gas, uint256_t{0x0ull});
            top[1] = uint256_t{0x40ull};
            top[2] = uint256_t{0x5e0ull};
            top += 2;
            MONAD_AOT_TAIL return b_1160<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_cf2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x60, 0x81, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x60, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1408u, 1440u, 138>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_cff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_cff(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x60, 0x71, 0x82, 0x10, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x60, 0x71, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(s0 < uint256_t{0x0ull, 0x0ull, 0x100ull, 0x0ull});
            bool const j6 = aot::nonzero(t1);
            uint256_t const m0 = s0;
            top[1] = m0;
            top[2] = uint256_t{0xb5ull};
            top += 2;
            if (j6) { MONAD_AOT_TAIL return b_d27<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_d1b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d1b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<128>(s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<64>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_d27<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d27(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x69, 0x82, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x69, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < uint256_t{0x0ull, 0x100ull, 0x0ull, 0x0ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_d45<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_d39<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d39(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<64>(s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<32>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_d45<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d45(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x65, 0x82, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x65, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < uint256_t{0x10000000000ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_d5f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_d53<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d53(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<32>(s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<16>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_d5f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d5f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x82, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < uint256_t{0x1000000ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_d77<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_d6b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d6b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<16>(s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<8>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_d77<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d77(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x62, 0x82, 0x01, 0x81, 0x02, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x83, 0x04, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x10, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x90, 0x50, 0x90, 0x50, 0x80, 0x60, 0x1c, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x62, 0x82, 0x01, 0x81, 0x02, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x83, 0x04, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x10, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x90, 0x50, 0x90, 0x50, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x10000ull};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::mul(s0, t1);
            uint256_t const t3 = aot::shr_c<18>(t2);
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = aot::udiv(s2, t3);
            uint256_t const t5 = t4 + t3;
            uint256_t const t6 = aot::shr_c<1>(t5);
            uint256_t const t7 = aot::udiv(s2, t6);
            uint256_t const t8 = t7 + t6;
            uint256_t const t9 = aot::shr_c<1>(t8);
            uint256_t const t10 = aot::udiv(s2, t9);
            uint256_t const t11 = t10 + t9;
            uint256_t const t12 = aot::shr_c<1>(t11);
            uint256_t const t13 = aot::udiv(s2, t12);
            uint256_t const t14 = t13 + t12;
            uint256_t const t15 = aot::shr_c<1>(t14);
            uint256_t const t16 = aot::udiv(s2, t15);
            uint256_t const t17 = t16 + t15;
            uint256_t const t18 = aot::shr_c<1>(t17);
            uint256_t const t19 = aot::udiv(s2, t18);
            uint256_t const t20 = t19 + t18;
            uint256_t const t21 = aot::shr_c<1>(t20);
            uint256_t const t22 = aot::udiv(s2, t21);
            uint256_t const t23 = t22 + t21;
            uint256_t const t24 = aot::shr_c<1>(t23);
            uint256_t const t25 = aot::udiv(s2, t24);
            uint256_t const t26 = t25 ^ t24;
            uint256_t const t27 = aot::from_bool(t24 < t25);
            uint256_t const t28 = aot::mul(t27, t26);
            uint256_t const t29 = t28 ^ t25;
            uint256_t const t30 = aot::shr_c<255>(t29);
            bool const j97 = aot::nonzero(t30);
            top[-2] = t29;
            top += -2;
            if (j97) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_de7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_de7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1440u, 1472u, 142>(ctx, gas, s0);
            top += -1;
            MONAD_AOT_TAIL return b_deb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_deb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x61, 0x52, 0x60, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x61, 0x52, 0x60, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1472u, 1504u, 145>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t1 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x1ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j10 = aot::nonzero(t3);
            if (j10) { MONAD_AOT_TAIL return b_e80<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_dfe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_dfe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x7f, 0x81, 0x14, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x7f, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t2 = aot::from_bool(t1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            bool const j6 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j6) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_e29<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e29(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x03, 0x60, 0x81, 0x12, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x03, 0x60, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            bool const j6 = aot::nonzero(t2);
            top[0] = t1;
            if (j6) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_e34<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e34(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, s0);
            top[0] = uint256_t{0xe41ull};
            top[1] = uint256_t{0x5e0ull};
            top += 1;
            MONAD_AOT_TAIL return b_1fa0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_e41(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1504u, 1536u, 148>(ctx, gas);
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_e4e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e4e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x81, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(s0 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_e75<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e75(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x03, 0x61, 0x52, 0x61, 0x56}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x03, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            aot::mstore_c<traits, 1472u, 1504u, 145>(ctx, gas, t1);
            top += -1;
            MONAD_AOT_TAIL return b_eab<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_e80(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x60, 0x81, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x60, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_e8d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e8d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, s0);
            top[0] = uint256_t{0xe9aull};
            top[1] = uint256_t{0x5e0ull};
            top += 1;
            MONAD_AOT_TAIL return b_1fa0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_e9a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1504u, 1536u, 148>(ctx, gas);
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_ea7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ea7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1472u, 1504u, 145>(ctx, gas, s0);
            top += -1;
            MONAD_AOT_TAIL return b_eab<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_eab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x61, 0x52, 0x60, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x61, 0x52, 0x60, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1504u, 1536u, 148>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t1 = aot::mload_c<traits, 1312u, 1344u, 129>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x1ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j10 = aot::nonzero(t3);
            if (j10) { MONAD_AOT_TAIL return b_f1e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_ebe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ebe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x03, 0x60, 0x81, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x03, 0x60, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1312u, 1344u, 129>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1440u, 1472u, 142>(ctx, gas);
            uint256_t const t3 = t2 - t1;
            uint256_t const t4 = aot::from_bool(slt(t3, uint256_t{0x0ull}));
            bool const j9 = aot::nonzero(t4);
            top[1] = t3;
            top += 1;
            if (j9) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_ecf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ecf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1c, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1c, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shr_c<1>(s0);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t1);
            top[0] = uint256_t{0xedfull};
            top[1] = uint256_t{0x600ull};
            top += 1;
            MONAD_AOT_TAIL return b_1fa0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_edf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1536u, 1568u, 151>(ctx, gas);
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_eec<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_eec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x81, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(s0 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_f13<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f13(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x03, 0x61, 0x52, 0x61, 0x56}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x03, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            aot::mstore_c<traits, 1504u, 1536u, 148>(ctx, gas, t1);
            top += -1;
            MONAD_AOT_TAIL return b_f54<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f1e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x01, 0x60, 0x81, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x01, 0x60, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1440u, 1472u, 142>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1312u, 1344u, 129>(ctx, gas);
            uint256_t const t3 = t2 + t1;
            uint256_t const t4 = aot::from_bool(slt(t3, uint256_t{0x0ull}));
            bool const j10 = aot::nonzero(t4);
            top[1] = t3;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_f30<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f30(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x60, 0x1c, 0x90, 0x50, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x60, 0x1c, 0x90, 0x50, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shr_c<1>(s0);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t1);
            top[0] = uint256_t{0xf43ull};
            top[1] = uint256_t{0x600ull};
            top += 1;
            MONAD_AOT_TAIL return b_1fa0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f43(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1536u, 1568u, 151>(ctx, gas);
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_f50<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f50(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1504u, 1536u, 148>(ctx, gas, s0);
            top += -1;
            MONAD_AOT_TAIL return b_f54<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f54(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x61, 0x51, 0x67, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}, 0, 7));
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x61, 0x51, 0x67, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1504u, 1536u, 148>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1472u, 1504u, 145>(ctx, gas);
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x597d89b3754abea0ull, 0xb504f333f9de6484ull, 0x0ull, 0x0ull}));
            uint256_t const t4 = aot::from_bool(slt(uint256_t{0xa682764c8ab54160ull, 0x4afb0ccc06219b7bull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t2));
            uint256_t const t5 = t4 & t3;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j16 = aot::nonzero(t6);
            top[1] = uint256_t{0xde0b6b3a7640000ull};
            top[2] = t1;
            top[3] = uint256_t{0xde0b6b3a7640000ull};
            top[4] = t2;
            top += 4;
            if (j16) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_fab<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_fab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x05, 0x02, 0x05, 0x61, 0x52, 0x61, 0x51, 0x67, 0x02, 0x61, 0x51, 0x67, 0x02, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x05, 0x02, 0x05, 0x61, 0x52, 0x61, 0x51, 0x67, 0x02, 0x61, 0x51, 0x67, 0x02, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::exp_c<0x2u>(s0);
            uint256_t const &s1 = top[-1];
            uint256_t r5;
            runtime::sdiv(&r5, &t1, &s1);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = aot::mul(r5, s2);
            uint256_t const &s3 = top[-3];
            uint256_t r7;
            runtime::sdiv(&r7, &t2, &s3);
            aot::mstore_c<traits, 1536u, 1568u, 151>(ctx, gas, r7);
            uint256_t const t3 = aot::mload_c<traits, 1536u, 1568u, 151>(ctx, gas);
            uint256_t const t4 = aot::mul(uint256_t{0xde0b6b3a7640000ull}, t3);
            uint256_t const t5 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t6 = aot::mul(uint256_t{0xde0b6b3a7640000ull}, t5);
            uint256_t const t7 = t4 - t6;
            uint256_t const t8 = aot::from_bool(slt(t4, t7));
            uint256_t const t9 = aot::from_bool(slt(t6, uint256_t{0x0ull}));
            uint256_t const t10 = t9 ^ t8;
            bool const j29 = aot::nonzero(t10);
            top[-3] = t4;
            top[-2] = t6;
            top[-1] = t7;
            top += -1;
            if (j29) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_fe3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_fe3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x67, 0x02, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x67, 0x02, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t2 = aot::mul(uint256_t{0xde0b6b3a7640000ull}, t1);
            uint256_t const t3 = aot::mload_c<traits, 1536u, 1568u, 151>(ctx, gas);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j13 = aot::nonzero(t4);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t2;
            top[0] = t3;
            if (j13) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_fff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_fff(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t r2;
            runtime::sdiv(&r2, &s1, &s0);
            uint256_t const t1 = aot::from_bool(s1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(s0 == uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = t4 | t2;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j17 = aot::nonzero(t6);
            top[1] = r2;
            top += 1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1016<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1016(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1280u, 1312u, 126>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::mul(s0, t1);
            uint256_t const t3 = ~t1;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(s0 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t1));
            uint256_t r25;
            runtime::sdiv(&r25, &t2, &t1);
            uint256_t const t10 = aot::from_bool(r25 == s0);
            uint256_t const t11 = t10 | t9;
            uint256_t const t12 = t11 & t8;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t12));
            bool const j31 = aot::nonzero(t13);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = t2;
            if (j31) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_103c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_103c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x60, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s3 - s0;
            uint256_t const t2 = aot::from_bool(slt(s3, t1));
            uint256_t const t3 = aot::from_bool(slt(s0, uint256_t{0x0ull}));
            uint256_t const t4 = t3 ^ t2;
            bool const j15 = aot::nonzero(t4);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j15) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_104f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_104f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x60, 0x02, 0x80, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x60, 0x02, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1152u, 1184u, 113>(ctx, gas);
            uint256_t const t2 = aot::mul(uint256_t{0x3ull}, t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j11 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t2;
            top += -1;
            if (j11) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1060<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1060(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x60, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t r2;
            runtime::sdiv(&r2, &s1, &s0);
            uint256_t const t1 = aot::from_bool(s1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(s0 == uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = t4 | t2;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j17 = aot::nonzero(t6);
            top[1] = r2;
            top += 1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1077<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1077(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x67, 0x60, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x67, 0x60, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1568u, 1600u, 154>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 992u, 1024u, 98>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 960u, 992u, 94>(ctx, gas);
            uint256_t const t4 = aot::from_bool(slt(t3, uint256_t{0x597d89b3754abea0ull, 0xb504f333f9de6484ull, 0x0ull, 0x0ull}));
            uint256_t const t5 = aot::from_bool(slt(uint256_t{0xa682764c8ab54160ull, 0x4afb0ccc06219b7bull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t3));
            uint256_t const t6 = t5 & t4;
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            bool const j23 = aot::nonzero(t7);
            top[-2] = uint256_t{0xde0b6b3a7640000ull};
            top[-1] = uint256_t{0x4ull};
            top[0] = t1;
            top[1] = t2;
            top[2] = t3;
            top += 2;
            if (j23) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_10d2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10d2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x05, 0x02, 0x05, 0x05, 0x60, 0x81, 0x12, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x05, 0x02, 0x05, 0x05, 0x60, 0x81, 0x12, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::exp_c<0x2u>(s0);
            uint256_t const &s1 = top[-1];
            uint256_t r5;
            runtime::sdiv(&r5, &t1, &s1);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = aot::mul(r5, s2);
            uint256_t const &s3 = top[-3];
            uint256_t r7;
            runtime::sdiv(&r7, &t2, &s3);
            uint256_t const &s4 = top[-4];
            uint256_t r8;
            runtime::sdiv(&r8, &r7, &s4);
            uint256_t const t3 = aot::from_bool(slt(r8, uint256_t{0x0ull}));
            bool const j13 = aot::nonzero(t3);
            top[-4] = r8;
            top += -4;
            if (j13) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_10e4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10e4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x12, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1600u, 1632u, 158>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            bool const j8 = aot::nonzero(t2);
            top[0] = t1;
            if (j8) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_10f4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10f4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x60, 0x35, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x60, 0x35, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1632u, 1664u, 161>(ctx, gas, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t2 = aot::mload_c<traits, 1600u, 1632u, 158>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = aot::udiv(t3, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t5 = t4 ^ t2;
            bool const j15 = aot::nonzero(t5);
            top[0] = t1;
            top[1] = t2;
            top[2] = t3;
            top += 2;
            if (j15) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_111b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_111b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x04, 0x61, 0x52, 0x61, 0x51, 0x6e, 0x04, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x04, 0x61, 0x52, 0x61, 0x51, 0x6e, 0x04, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::udiv(s0, s2);
            aot::mstore_c<traits, 1664u, 1696u, 164>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t3 = aot::udiv(uint256_t{0xd9a5cf8800000000ull, 0x604be73de4838aull, 0x0ull, 0x0ull}, t2);
            uint256_t const t4 = aot::mload_c<traits, 1664u, 1696u, 164>(ctx, gas);
            uint256_t const t5 = aot::from_bool(t4 < t3);
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j14 = aot::nonzero(t6);
            top += -3;
            if (j14) { MONAD_AOT_TAIL return b_1147<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1141<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1141(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_1155<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1147(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x60, 0x1c, 0x61, 0x51, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x60, 0x1c, 0x61, 0x51, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t2 = aot::shr_c<1>(t1);
            uint256_t const t3 = aot::mload_c<traits, 1664u, 1696u, 164>(ctx, gas);
            uint256_t const t4 = aot::from_bool(t2 < t3);
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            top[1] = t5;
            top += 1;
            MONAD_AOT_TAIL return b_1155<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1155(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_115b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_115b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x40ull};
            top[2] = uint256_t{0x640ull};
            top += 2;
            MONAD_AOT_TAIL return b_1160<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1160(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0xf3}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            aot::finish(ctx, gas, StatusCode::Success, s0, s1);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1166(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0xb0872d5dull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1185<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1172<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1172(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x34, 0x17, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x34, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x84ull});
            uint256_t const t3 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t4 = t3 | t2;
            bool const j6 = aot::nonzero(t4);
            if (j6) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_117c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_117c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, uint256_t{0x0ull});
            MONAD_AOT_TAIL return b_141f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1185(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0x81d18d87ull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1e7c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1191<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1191(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x34, 0x17, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x34, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x24ull});
            uint256_t const t3 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t4 = t3 | t2;
            bool const j6 = aot::nonzero(t4);
            if (j6) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_119b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_119b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x60, 0x52, 0x7f, 0x60, 0x35, 0x13, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x60, 0x52, 0x7f, 0x60, 0x35, 0x13, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t1);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t3 = aot::from_bool(slt(uint256_t{0xb731c958f34d94c1ull, 0xfffffffffffffffdull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t2));
            bool const j9 = aot::nonzero(t3);
            if (j9) { MONAD_AOT_TAIL return b_11d7<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_11ca<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11ca(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x52, 0x60, 0x60, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x52, 0x60, 0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, uint256_t{0x0ull});
            top[1] = uint256_t{0x20ull};
            top[2] = uint256_t{0x60ull};
            top += 2;
            MONAD_AOT_TAIL return b_13fd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_11d7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x68, 0x60, 0x35, 0x13, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x68, 0x60, 0x35, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(slt(uint256_t{0x55bf798b4a1bf1e4ull, 0x7ull, 0x0ull, 0x0ull}, t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_1247<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_11eb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11eb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x52, 0x7f, 0x60, 0x52, 0x60, 0x50, 0x60, 0x51, 0x80, 0x60, 0x01, 0x60, 0x82, 0x60, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x60, 0x52, 0x60, 0x60, 0x52, 0x60, 0x19, 0x60, 0x60, 0x51, 0x01, 0x16, 0x60, 0x01, 0x60, 0xfd}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x52, 0x7f, 0x60, 0x52, 0x60, 0x50, 0x60, 0x51, 0x80, 0x60, 0x01, 0x60, 0x82, 0x60, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x60, 0x52, 0x60, 0x60, 0x52, 0x60, 0x19, 0x60, 0x60, 0x51, 0x01, 0x16, 0x60, 0x01, 0x60, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, uint256_t{0x16ull});
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, uint256_t{0x0ull, 0x6572666c6f770000ull, 0x645f657870206f76ull, 0x4d6174683a207761ull});
            uint256_t const t1 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t2 = uint256_t{0x80ull} + t1;
            uint256_t const t3 = uint256_t{0x0ull} - t1;
            uint256_t const t4 = t3 & uint256_t{0x1full};
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t2, &t5, &t4);
            gas = ctx->gas_remaining;
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x8c379a0ull});
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, uint256_t{0x20ull});
            uint256_t const t6 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t7 = t6 + uint256_t{0x1full};
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t9 = uint256_t{0x44ull} + t8;
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x3cull}, t9);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1247(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x65, 0x60, 0x35, 0x60, 0x1b, 0x05, 0x60, 0x52, 0x6b, 0x6b, 0x60, 0x51, 0x60, 0x1b, 0x05, 0x01, 0x60, 0x1d, 0x60, 0x52, 0x6b, 0x60, 0x51, 0x02, 0x60, 0x51, 0x03, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x6c, 0x60, 0x51, 0x01, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x79, 0x60, 0x51, 0x6e, 0x60, 0x51, 0x6d, 0x60, 0x51, 0x60, 0x51, 0x01, 0x03, 0x02, 0x60, 0x1d, 0x01, 0x02, 0x01, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x6c, 0x60, 0x51, 0x03, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x03, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x6e, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x03, 0x60, 0x52, 0x6e, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x60, 0x51, 0x60, 0x51, 0x05, 0x60, 0x52, 0x74, 0x60, 0x51, 0x02, 0x60, 0x51, 0x60, 0x03, 0x60, 0x81, 0x12, 0x61, 0x57}, 0, 7));
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x65, 0x60, 0x35, 0x60, 0x1b, 0x05, 0x60, 0x52, 0x6b, 0x6b, 0x60, 0x51, 0x60, 0x1b, 0x05, 0x01, 0x60, 0x1d, 0x60, 0x52, 0x6b, 0x60, 0x51, 0x02, 0x60, 0x51, 0x03, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x6c, 0x60, 0x51, 0x01, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x79, 0x60, 0x51, 0x6e, 0x60, 0x51, 0x6d, 0x60, 0x51, 0x60, 0x51, 0x01, 0x03, 0x02, 0x60, 0x1d, 0x01, 0x02, 0x01, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x6c, 0x60, 0x51, 0x03, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x03, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x6e, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x03, 0x60, 0x52, 0x6e, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x60, 0x51, 0x60, 0x51, 0x05, 0x60, 0x52, 0x74, 0x60, 0x51, 0x02, 0x60, 0x51, 0x60, 0x03, 0x60, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::shl_c<78>(t1);
            uint256_t const k6_1 = uint256_t{0x3782dace9d9ull};
            uint256_t r6;
            runtime::sdiv(&r6, &t2, &k6_1);
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, r6);
            uint256_t const t3 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t4 = aot::shl_c<96>(t3);
            uint256_t const k15_1 = uint256_t{0xd1cf79abc9e3b398ull, 0xb17217f7ull, 0x0ull, 0x0ull};
            uint256_t r15;
            runtime::sdiv(&r15, &t4, &k15_1);
            uint256_t const t5 = r15 + uint256_t{0x0ull, 0x80000000ull, 0x0ull, 0x0ull};
            uint256_t const t6 = sar(uint256_t{0x60ull}, t5);
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, t6);
            uint256_t const t7 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t8 = aot::mul(t7, uint256_t{0xd1cf79abc9e3b398ull, 0xb17217f7ull, 0x0ull, 0x0ull});
            uint256_t const t9 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t10 = t9 - t8;
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t10);
            uint256_t const t11 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t12 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t13 = t12 + uint256_t{0x37d0007b713f7650ull, 0x10fe68e7fdull, 0x0ull, 0x0ull};
            uint256_t const t14 = aot::mul(t13, t11);
            uint256_t const t15 = sar(uint256_t{0x60ull}, t14);
            uint256_t const t16 = t15 + uint256_t{0xd19bf614176fe9eaull, 0x2d16720577bull, 0x0ull, 0x0ull};
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t16);
            uint256_t const t17 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t18 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t19 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t20 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t21 = t20 + t19;
            uint256_t const t22 = t21 - uint256_t{0x96949216d2255a6cull, 0x4a4fd9f2a8bull, 0x0ull, 0x0ull};
            uint256_t const t23 = aot::mul(t22, t18);
            uint256_t const t24 = sar(uint256_t{0x60ull}, t23);
            uint256_t const t25 = t24 + uint256_t{0x9d25fcb740196450ull, 0x587f503bb6ea2ull, 0x0ull, 0x0ull};
            uint256_t const t26 = aot::mul(t25, t17);
            uint256_t const t27 = t26 + uint256_t{0x0ull, 0x3b2ca45c00000000ull, 0xebba824c98fb31b8ull, 0xd835ull};
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t27);
            uint256_t const t28 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t29 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t30 = t29 - uint256_t{0xb2d9cbaf0fd5aafcull, 0x240c330e9full, 0x0ull, 0x0ull};
            uint256_t const t31 = aot::mul(t30, t28);
            uint256_t const t32 = sar(uint256_t{0x60ull}, t31);
            uint256_t const t33 = t32 + uint256_t{0xc85f6e2461837cd9ull, 0x277594991cfull, 0x0ull, 0x0ull};
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t33);
            uint256_t const t34 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t35 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t36 = aot::mul(t35, t34);
            uint256_t const t37 = sar(uint256_t{0x60ull}, t36);
            uint256_t const t38 = t37 - uint256_t{0x6a5061b25ef1c9c4ull, 0x1a521255e34full, 0x0ull, 0x0ull};
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t38);
            uint256_t const t39 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t40 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t41 = aot::mul(t40, t39);
            uint256_t const t42 = sar(uint256_t{0x60ull}, t41);
            uint256_t const t43 = t42 + uint256_t{0xcf962f1a1d3db4a5ull, 0xb1bbb201f443ull, 0x0ull, 0x0ull};
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t43);
            uint256_t const t44 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t45 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t46 = aot::mul(t45, t44);
            uint256_t const t47 = sar(uint256_t{0x60ull}, t46);
            uint256_t const t48 = t47 - uint256_t{0x51a9331fed693f15ull, 0x2c72388d9f74full, 0x0ull, 0x0ull};
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t48);
            uint256_t const t49 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t50 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t51 = aot::mul(t50, t49);
            uint256_t const t52 = sar(uint256_t{0x60ull}, t51);
            uint256_t const t53 = t52 + uint256_t{0x47a8a8cb2a527d57ull, 0x5180bb14799abull, 0x0ull, 0x0ull};
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t53);
            uint256_t const t54 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t55 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t r125;
            runtime::sdiv(&r125, &t55, &t54);
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, r125);
            uint256_t const t56 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t57 = aot::mul(t56, uint256_t{0xee70ef65f9978af3ull, 0x63c32e5c2f6dc192ull, 0x29d9dc385ull, 0x0ull});
            uint256_t const t58 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t59 = uint256_t{0xc3ull} - t58;
            uint256_t const t60 = aot::from_bool(slt(t59, uint256_t{0x0ull}));
            bool const j140 = aot::nonzero(t60);
            top[1] = t57;
            top[2] = t59;
            top += 2;
            if (j140) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_13eb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_13eb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x1c, 0x80, 0x60, 0x1c, 0x61, 0x57}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x1c, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr(s0, s1);
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j5 = aot::nonzero(t2);
            top[-1] = t1;
            top += -1;
            if (j5) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_13f4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_13f4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x60, 0x61}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x60, 0x61}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 256u, 288u, 27>(ctx, gas, s0);
            top[0] = uint256_t{0x20ull};
            top[1] = uint256_t{0x100ull};
            top += 1;
            MONAD_AOT_TAIL return b_13fd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_13fd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0xf3}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            aot::finish(ctx, gas, StatusCode::Success, s0, s1);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1403(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0xe6864766ull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1be8<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_140f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_140f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x34, 0x17, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x34, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xa4ull});
            uint256_t const t3 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t4 = t3 | t2;
            bool const j6 = aot::nonzero(t4);
            if (j6) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1419<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1419(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x84ull});
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t1);
            MONAD_AOT_TAIL return b_141f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_141f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xfa0ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_1432<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_142c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_142c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_143d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1432(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x60, 0x35, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x60, 0x35, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0x2625a00ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_143d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_143d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1443<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1443(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x64, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x64, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x2540be400ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_1458<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1452<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1452(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_1467<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1458(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x60, 0x35, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x60, 0x35, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0x2c2fd72164d8000ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_1467<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1467(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_146d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_146d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x60, 0x37, 0x60, 0x51, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x60, 0x37, 0x60, 0x51, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const k3_0 = uint256_t{0x60ull};
            uint256_t const k3_1 = uint256_t{0x44ull};
            uint256_t const k3_2 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k3_0, &k3_1, &k3_2);
            gas = ctx->gas_remaining;
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t2 < t1);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j11 = aot::nonzero(t4);
            if (j11) { MONAD_AOT_TAIL return b_148c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1480<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1480(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x60, 0x52, 0x60, 0x35, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x60, 0x52, 0x60, 0x35, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x64ull});
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, t1);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x44ull});
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_148c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_148c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x3b9aca00ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_14a1<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_149b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_149b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_14b6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_14a1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x6d, 0x60, 0x51, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x6d, 0x60, 0x51, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t2 = aot::from_bool(uint256_t{0x38c15b0a00000000ull, 0x314dc6448d93ull, 0x0ull, 0x0ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_14b6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_14b6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_14bc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14bc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x65, 0x60, 0x51, 0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 0, 7));
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x65, 0x60, 0x51, 0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = aot::udiv(t3, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t5 = t4 ^ t2;
            bool const j14 = aot::nonzero(t5);
            top[1] = uint256_t{0x5af3107a4000ull};
            top[2] = t1;
            top[3] = t2;
            top[4] = t3;
            top += 4;
            if (j14) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_14e5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14e5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x04, 0x10, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x04, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::udiv(s0, s2);
            uint256_t const &s3 = top[-3];
            uint256_t const t2 = aot::from_bool(t1 < s3);
            bool const j5 = aot::nonzero(t2);
            top += -4;
            if (j5) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_14ed<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14ed(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x60, 0x51, 0x01, 0x60, 0x52, 0x60, 0x60, 0x52, 0x60, 0x51, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x60, 0x51, 0x01, 0x60, 0x52, 0x60, 0x60, 0x52, 0x60, 0x51, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t3 = t2 + t1;
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t3);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t4 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            bool const j13 = aot::nonzero(t4);
            if (j13) { MONAD_AOT_TAIL return b_1601<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1503<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1503(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x60, 0x51, 0x02, 0x80, 0x60, 0x71, 0x82, 0x10, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x60, 0x51, 0x02, 0x80, 0x60, 0x71, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, t1);
            uint256_t const t4 = aot::from_bool(t3 < uint256_t{0x0ull, 0x0ull, 0x100ull, 0x0ull});
            bool const j11 = aot::nonzero(t4);
            top[1] = t3;
            top[2] = t3;
            top[3] = uint256_t{0xb5ull};
            top += 3;
            if (j11) { MONAD_AOT_TAIL return b_1532<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1526<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1526(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<128>(s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<64>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_1532<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1532(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x69, 0x82, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x69, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < uint256_t{0x0ull, 0x100ull, 0x0ull, 0x0ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1550<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1544<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1544(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<64>(s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<32>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_1550<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1550(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x65, 0x82, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x65, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < uint256_t{0x10000000000ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_156a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_155e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_155e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<32>(s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<16>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_156a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_156a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x82, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < uint256_t{0x1000000ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1582<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1576<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1576(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<16>(s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<8>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_1582<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1582(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x62, 0x82, 0x01, 0x81, 0x02, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x83, 0x04, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x10, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x90, 0x50, 0x90, 0x50, 0x80, 0x60, 0x1b, 0x81, 0x81, 0x60, 0x1c, 0x18, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x62, 0x82, 0x01, 0x81, 0x02, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x83, 0x04, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x10, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x90, 0x50, 0x90, 0x50, 0x80, 0x60, 0x1b, 0x81, 0x81, 0x60, 0x1c, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x10000ull};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::mul(s0, t1);
            uint256_t const t3 = aot::shr_c<18>(t2);
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = aot::udiv(s2, t3);
            uint256_t const t5 = t4 + t3;
            uint256_t const t6 = aot::shr_c<1>(t5);
            uint256_t const t7 = aot::udiv(s2, t6);
            uint256_t const t8 = t7 + t6;
            uint256_t const t9 = aot::shr_c<1>(t8);
            uint256_t const t10 = aot::udiv(s2, t9);
            uint256_t const t11 = t10 + t9;
            uint256_t const t12 = aot::shr_c<1>(t11);
            uint256_t const t13 = aot::udiv(s2, t12);
            uint256_t const t14 = t13 + t12;
            uint256_t const t15 = aot::shr_c<1>(t14);
            uint256_t const t16 = aot::udiv(s2, t15);
            uint256_t const t17 = t16 + t15;
            uint256_t const t18 = aot::shr_c<1>(t17);
            uint256_t const t19 = aot::udiv(s2, t18);
            uint256_t const t20 = t19 + t18;
            uint256_t const t21 = aot::shr_c<1>(t20);
            uint256_t const t22 = aot::udiv(s2, t21);
            uint256_t const t23 = t22 + t21;
            uint256_t const t24 = aot::shr_c<1>(t23);
            uint256_t const t25 = aot::udiv(s2, t24);
            uint256_t const t26 = t25 ^ t24;
            uint256_t const t27 = aot::from_bool(t24 < t25);
            uint256_t const t28 = aot::mul(t27, t26);
            uint256_t const t29 = t28 ^ t25;
            uint256_t const t30 = aot::shl_c<1>(t29);
            uint256_t const t31 = aot::shr_c<1>(t30);
            uint256_t const t32 = t31 ^ t29;
            bool const j102 = aot::nonzero(t32);
            top[-2] = t29;
            top[-1] = t30;
            top += -1;
            if (j102) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_15f8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_15f8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x52, 0x61, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, s0);
            top += -2;
            MONAD_AOT_TAIL return b_170f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1601(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x60, 0x51, 0x60, 0x51, 0x60, 0x51, 0x60, 0x1b, 0x02, 0x04, 0x02, 0x80, 0x60, 0x71, 0x82, 0x10, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x60, 0x51, 0x60, 0x51, 0x60, 0x51, 0x60, 0x1b, 0x02, 0x04, 0x02, 0x80, 0x60, 0x71, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t4 = aot::shl_c<2>(t3);
            uint256_t const t5 = aot::mul(t4, t2);
            uint256_t const t6 = aot::udiv(t5, t1);
            uint256_t const t7 = aot::mul(t6, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t8 = aot::from_bool(t7 < uint256_t{0x0ull, 0x0ull, 0x100ull, 0x0ull});
            bool const j19 = aot::nonzero(t8);
            top[1] = t7;
            top[2] = t7;
            top[3] = uint256_t{0xb5ull};
            top += 3;
            if (j19) { MONAD_AOT_TAIL return b_1642<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1636<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1636(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<128>(s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<64>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_1642<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1642(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x69, 0x82, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x69, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < uint256_t{0x0ull, 0x100ull, 0x0ull, 0x0ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1660<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1654<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1654(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<64>(s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<32>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_1660<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1660(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x65, 0x82, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x65, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < uint256_t{0x10000000000ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_167a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_166e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_166e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<32>(s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<16>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_167a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_167a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x82, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < uint256_t{0x1000000ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1692<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1686<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1686(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x1c, 0x91, 0x50, 0x80, 0x60, 0x1b, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<16>(s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<8>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_1692<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1692(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x62, 0x82, 0x01, 0x81, 0x02, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x83, 0x04, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x10, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x90, 0x50, 0x90, 0x50, 0x60, 0x52, 0x60, 0x51, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x62, 0x82, 0x01, 0x81, 0x02, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x81, 0x84, 0x04, 0x01, 0x60, 0x1c, 0x90, 0x50, 0x80, 0x83, 0x04, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x10, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x90, 0x50, 0x90, 0x50, 0x60, 0x52, 0x60, 0x51, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x10000ull};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::mul(s0, t1);
            uint256_t const t3 = aot::shr_c<18>(t2);
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = aot::udiv(s2, t3);
            uint256_t const t5 = t4 + t3;
            uint256_t const t6 = aot::shr_c<1>(t5);
            uint256_t const t7 = aot::udiv(s2, t6);
            uint256_t const t8 = t7 + t6;
            uint256_t const t9 = aot::shr_c<1>(t8);
            uint256_t const t10 = aot::udiv(s2, t9);
            uint256_t const t11 = t10 + t9;
            uint256_t const t12 = aot::shr_c<1>(t11);
            uint256_t const t13 = aot::udiv(s2, t12);
            uint256_t const t14 = t13 + t12;
            uint256_t const t15 = aot::shr_c<1>(t14);
            uint256_t const t16 = aot::udiv(s2, t15);
            uint256_t const t17 = t16 + t15;
            uint256_t const t18 = aot::shr_c<1>(t17);
            uint256_t const t19 = aot::udiv(s2, t18);
            uint256_t const t20 = t19 + t18;
            uint256_t const t21 = aot::shr_c<1>(t20);
            uint256_t const t22 = aot::udiv(s2, t21);
            uint256_t const t23 = t22 + t21;
            uint256_t const t24 = aot::shr_c<1>(t23);
            uint256_t const t25 = aot::udiv(s2, t24);
            uint256_t const t26 = t25 ^ t24;
            uint256_t const t27 = aot::from_bool(t24 < t25);
            uint256_t const t28 = aot::mul(t27, t26);
            uint256_t const t29 = t28 ^ t25;
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t29);
            uint256_t const t30 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t31 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t32 = aot::from_bool(t31 < t30);
            uint256_t const t33 = aot::from_bool(!aot::nonzero(t32));
            bool const j102 = aot::nonzero(t33);
            top += -3;
            if (j102) { MONAD_AOT_TAIL return b_170f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1709<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1709(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t1);
            MONAD_AOT_TAIL return b_170f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_170f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x67, 0x81, 0x01, 0x81, 0x81, 0x10, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x67, 0x81, 0x01, 0x81, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = t1 + uint256_t{0xde0b6b3a7640000ull};
            uint256_t const t3 = aot::from_bool(t2 < t1);
            bool const j10 = aot::nonzero(t3);
            top[1] = t1;
            top[2] = t2;
            top += 2;
            if (j10) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1725<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1725(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x52, 0x60, 0x61, 0x52, 0x60, 0x60, 0x90}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x52, 0x60, 0x61, 0x52, 0x60, 0x60, 0x90}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, s0);
            aot::mstore_c<traits, 256u, 288u, 27>(ctx, gas, uint256_t{0x0ull});
            top[-1] = uint256_t{0xffull};
            top[0] = uint256_t{0x0ull};
            MONAD_AOT_TAIL return b_1735<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1735(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x52, 0x60, 0x51, 0x61, 0x52, 0x60, 0x51, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x52, 0x60, 0x51, 0x61, 0x52, 0x60, 0x51, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 288u, 320u, 30>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j12 = aot::nonzero(t3);
            if (j12) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_174a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_174a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x60, 0x51, 0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 0, 7));
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x60, 0x51, 0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t4 = aot::mul(t3, uint256_t{0x3782dace9d900000ull});
            uint256_t const t5 = aot::udiv(t4, uint256_t{0x3782dace9d900000ull});
            uint256_t const t6 = t5 ^ t3;
            bool const j15 = aot::nonzero(t6);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top[4] = t4;
            top += 4;
            if (j15) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_176f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_176f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x04, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x04, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::udiv(s0, s2);
            uint256_t const t2 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::udiv(t3, t2);
            uint256_t const t6 = aot::from_bool(t5 == t1);
            uint256_t const t7 = t6 | t4;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j18 = aot::nonzero(t8);
            top[-2] = t1;
            top[-1] = t2;
            top[0] = t3;
            if (j18) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1785<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1785(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x52, 0x60, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x52, 0x60, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            aot::mstore_c<traits, 352u, 384u, 36>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            aot::mstore_c<traits, 384u, 416u, 39>(ctx, gas, t2);
            uint256_t const t3 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t4 = aot::mload_c<traits, 384u, 416u, 39>(ctx, gas);
            uint256_t const t5 = aot::from_bool(t3 < t4);
            bool const j17 = aot::nonzero(t5);
            top += -4;
            if (j17) { MONAD_AOT_TAIL return b_17b6<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_17a2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_17a2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x51, 0x61, 0x51, 0x03, 0x01, 0x61, 0x52, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x51, 0x61, 0x51, 0x03, 0x01, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 384u, 416u, 39>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t3 = t2 - t1;
            uint256_t const t4 = t3 + uint256_t{0x1ull};
            aot::mstore_c<traits, 384u, 416u, 39>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_17c7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_17b6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x61, 0x51, 0x61, 0x51, 0x03, 0x01, 0x61, 0x52}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x61, 0x51, 0x61, 0x51, 0x03, 0x01, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 384u, 416u, 39>(ctx, gas);
            uint256_t const t3 = t2 - t1;
            uint256_t const t4 = t3 + uint256_t{0x1ull};
            aot::mstore_c<traits, 384u, 416u, 39>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_17c7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_17c7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x60, 0x35, 0x60, 0x35, 0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 0, 8));
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x60, 0x35, 0x60, 0x35, 0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t4 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t5 = aot::mul(t4, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t6 = aot::udiv(t5, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t7 = t6 ^ t4;
            bool const j18 = aot::nonzero(t7);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top[4] = t4;
            top[5] = t5;
            top += 5;
            if (j18) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_17f0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_17f0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x04, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x04, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::udiv(s0, s2);
            uint256_t const t2 = aot::mload_c<traits, 384u, 416u, 39>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::udiv(t3, t2);
            uint256_t const t6 = aot::from_bool(t5 == t1);
            uint256_t const t7 = t6 | t4;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j18 = aot::nonzero(t8);
            top[-2] = t1;
            top[-1] = t2;
            top[0] = t3;
            if (j18) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1807<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1807(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mload_c<traits, 384u, 416u, 39>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::udiv(t3, t2);
            uint256_t const t6 = aot::from_bool(t5 == t1);
            uint256_t const t7 = t6 | t4;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j20 = aot::nonzero(t8);
            top[-3] = t1;
            top[-2] = t2;
            top[-1] = t3;
            top += -1;
            if (j20) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1820<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1820(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x81, 0x02, 0x81, 0x61, 0x82, 0x04, 0x18, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x81, 0x02, 0x81, 0x61, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(s0, uint256_t{0x2710ull});
            uint256_t const t2 = aot::udiv(t1, uint256_t{0x2710ull});
            uint256_t const t3 = t2 ^ s0;
            bool const j13 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j13) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1834<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1834(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x04, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x04, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::udiv(s0, s2);
            aot::mstore_c<traits, 416u, 448u, 42>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 384u, 416u, 39>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t4 = aot::mul(t3, uint256_t{0x3782dace9d900000ull});
            uint256_t const t5 = aot::udiv(t4, uint256_t{0x3782dace9d900000ull});
            uint256_t const t6 = t5 ^ t3;
            bool const j18 = aot::nonzero(t6);
            top[-2] = t2;
            top[-1] = t3;
            top[0] = t4;
            if (j18) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_185f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_185f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x04, 0x61, 0x52, 0x60, 0x51, 0x67, 0x60, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 3, 6));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x04, 0x61, 0x52, 0x60, 0x51, 0x67, 0x60, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::udiv(s0, s2);
            aot::mstore_c<traits, 448u, 480u, 45>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t4 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t5 = aot::mul(t3, t4);
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t7 = aot::udiv(t5, t4);
            uint256_t const t8 = aot::from_bool(t7 == t3);
            uint256_t const t9 = t8 | t6;
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            bool const j25 = aot::nonzero(t10);
            top[-2] = t2;
            top[-1] = uint256_t{0xde0b6b3a7640000ull};
            top[0] = t3;
            top[1] = t4;
            top[2] = t5;
            top += 2;
            if (j25) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1889<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1889(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = s4 + t1;
            uint256_t const t3 = aot::from_bool(t2 < s4);
            bool const j12 = aot::nonzero(t3);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j12) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1898<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1898(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x60, 0x1b, 0x81, 0x81, 0x60, 0x1c, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x60, 0x1b, 0x81, 0x81, 0x60, 0x1c, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 416u, 448u, 42>(ctx, gas);
            uint256_t const t2 = aot::shl_c<1>(t1);
            uint256_t const t3 = aot::shr_c<1>(t2);
            uint256_t const t4 = t3 ^ t1;
            bool const j15 = aot::nonzero(t4);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = t2;
            if (j15) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_18ae<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18ae(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_18ba<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18ba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s2 + t1;
            uint256_t const t3 = aot::from_bool(t2 < s2);
            bool const j14 = aot::nonzero(t3);
            top[-1] = t1;
            top[0] = t2;
            if (j14) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_18cb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18cb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x67, 0x61, 0x51, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 3, 6));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x67, 0x61, 0x51, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::udiv(t3, t2);
            uint256_t const t6 = aot::from_bool(t5 == t1);
            uint256_t const t7 = t6 | t4;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j22 = aot::nonzero(t8);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = uint256_t{0xde0b6b3a7640000ull};
            top[0] = t1;
            top[1] = t2;
            top[2] = t3;
            top += 2;
            if (j22) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_18ef<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18ef(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = s4 - t1;
            uint256_t const t3 = aot::from_bool(s4 < t2);
            bool const j12 = aot::nonzero(t3);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j12) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_18fe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18fe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x51, 0x61, 0x51, 0x60, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x51, 0x61, 0x51, 0x60, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 480u, 512u, 48>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 480u, 512u, 48>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t4 = t2 + t3;
            uint256_t const t5 = aot::from_bool(t4 < t2);
            bool const j19 = aot::nonzero(t5);
            top[-2] = t1;
            top[-1] = t2;
            top[0] = t3;
            top[1] = t4;
            top += 1;
            if (j19) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_191a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_191a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(s3, s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const t3 = aot::udiv(t1, s0);
            uint256_t const t4 = aot::from_bool(t3 == s3);
            uint256_t const t5 = t4 | t2;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j17 = aot::nonzero(t6);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_192e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_192e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 480u, 512u, 48>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_193c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_193c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x60, 0x51, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x60, 0x51, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 512u, 544u, 51>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 480u, 512u, 48>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t4 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t5 = aot::mul(t3, t4);
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t7 = aot::udiv(t5, t4);
            uint256_t const t8 = aot::from_bool(t7 == t3);
            uint256_t const t9 = t8 | t6;
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            bool const j28 = aot::nonzero(t10);
            top[-1] = t2;
            top[0] = t3;
            top[1] = t4;
            top[2] = t5;
            top += 2;
            if (j28) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1961<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1961(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x52, 0x67, 0x61, 0x51, 0x11, 0x15, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x52, 0x67, 0x61, 0x51, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            aot::mstore_c<traits, 544u, 576u, 54>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t3 = aot::from_bool(uint256_t{0xde0b6b3a763ffffull} < t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j13 = aot::nonzero(t4);
            top += -4;
            if (j13) { MONAD_AOT_TAIL return b_19e8<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_197d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_197d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x67, 0x60, 0x51, 0x61, 0x51, 0x61, 0x51, 0x04, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 0, 10));
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x67, 0x60, 0x51, 0x61, 0x51, 0x61, 0x51, 0x04, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t4 = aot::mload_c<traits, 480u, 512u, 48>(ctx, gas);
            uint256_t const t5 = aot::mload_c<traits, 416u, 448u, 42>(ctx, gas);
            uint256_t const t6 = aot::udiv(t5, t4);
            uint256_t const t7 = aot::mul(t3, t6);
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t9 = aot::udiv(t7, t6);
            uint256_t const t10 = aot::from_bool(t9 == t3);
            uint256_t const t11 = t10 | t8;
            uint256_t const t12 = aot::from_bool(!aot::nonzero(t11));
            bool const j25 = aot::nonzero(t12);
            top[1] = t1;
            top[2] = t2;
            top[3] = uint256_t{0xde0b6b3a7640000ull};
            top[4] = t3;
            top[5] = t6;
            top[6] = t7;
            top += 6;
            if (j25) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_19aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_19aa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x67, 0x61, 0x51, 0x03, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x67, 0x61, 0x51, 0x03, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t3 = t2 - uint256_t{0xde0b6b3a7640000ull};
            uint256_t const t4 = aot::mul(t1, t3);
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t6 = aot::udiv(t4, t3);
            uint256_t const t7 = aot::from_bool(t6 == t1);
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            bool const j22 = aot::nonzero(t9);
            top[-3] = t1;
            top[-2] = t3;
            top[-1] = t4;
            top += -1;
            if (j22) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_19cd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_19cd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = s4 - t1;
            uint256_t const t3 = aot::from_bool(s4 < t2);
            bool const j12 = aot::nonzero(t3);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j12) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_19dc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_19dc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 544u, 576u, 54>(ctx, gas, s0);
            top += -3;
            MONAD_AOT_TAIL return b_1a50<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_19e8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x67, 0x60, 0x51, 0x61, 0x51, 0x61, 0x51, 0x04, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 0, 10));
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x67, 0x60, 0x51, 0x61, 0x51, 0x61, 0x51, 0x04, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t4 = aot::mload_c<traits, 480u, 512u, 48>(ctx, gas);
            uint256_t const t5 = aot::mload_c<traits, 416u, 448u, 42>(ctx, gas);
            uint256_t const t6 = aot::udiv(t5, t4);
            uint256_t const t7 = aot::mul(t3, t6);
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t9 = aot::udiv(t7, t6);
            uint256_t const t10 = aot::from_bool(t9 == t3);
            uint256_t const t11 = t10 | t8;
            uint256_t const t12 = aot::from_bool(!aot::nonzero(t11));
            bool const j26 = aot::nonzero(t12);
            top[1] = t1;
            top[2] = t2;
            top[3] = uint256_t{0xde0b6b3a7640000ull};
            top[4] = t3;
            top[5] = t6;
            top[6] = t7;
            top += 6;
            if (j26) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1a16<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a16(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x51, 0x67, 0x03, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x51, 0x67, 0x03, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t3 = uint256_t{0xde0b6b3a7640000ull} - t2;
            uint256_t const t4 = aot::mul(t1, t3);
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t6 = aot::udiv(t4, t3);
            uint256_t const t7 = aot::from_bool(t6 == t1);
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            bool const j22 = aot::nonzero(t9);
            top[-3] = t1;
            top[-2] = t3;
            top[-1] = t4;
            top += -1;
            if (j22) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1a39<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a39(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = s4 + t1;
            uint256_t const t3 = aot::from_bool(t2 < s4);
            bool const j12 = aot::nonzero(t3);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j12) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1a48<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a48(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 544u, 576u, 54>(ctx, gas, s0);
            top += -3;
            MONAD_AOT_TAIL return b_1a50<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a50(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 512u, 544u, 51>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t1 < t2);
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_1a71<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1a5e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a5e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x03, 0x60, 0x1c, 0x60, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x03, 0x60, 0x1c, 0x60, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 512u, 544u, 51>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t3 = t2 - t1;
            uint256_t const t4 = aot::shr_c<1>(t3);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_1a7e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a71(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x03, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x03, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 512u, 544u, 51>(ctx, gas);
            uint256_t const t3 = t2 - t1;
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t3);
            MONAD_AOT_TAIL return b_1a7e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a7e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x60, 0x51, 0x11, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x60, 0x51, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t1 < t2);
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_1a9b<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1a8b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a8b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x61, 0x51, 0x03, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x61, 0x51, 0x03, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t3 = t2 - t1;
            aot::mstore_c<traits, 256u, 288u, 27>(ctx, gas, t3);
            MONAD_AOT_TAIL return b_1aa8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a9b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x60, 0x51, 0x03, 0x61, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x60, 0x51, 0x03, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t3 = t2 - t1;
            aot::mstore_c<traits, 256u, 288u, 27>(ctx, gas, t3);
            MONAD_AOT_TAIL return b_1aa8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1aa8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x80, 0x66, 0x81, 0x18, 0x82, 0x66, 0x11, 0x02, 0x18, 0x90, 0x50, 0x61, 0x51, 0x65, 0x81, 0x02, 0x81, 0x65, 0x82, 0x04, 0x18, 0x61, 0x57}, 0, 6));
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x80, 0x66, 0x81, 0x18, 0x82, 0x66, 0x11, 0x02, 0x18, 0x90, 0x50, 0x61, 0x51, 0x65, 0x81, 0x02, 0x81, 0x65, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = t1 ^ uint256_t{0x2386f26fc10000ull};
            uint256_t const t3 = aot::from_bool(t1 < uint256_t{0x2386f26fc10000ull});
            uint256_t const t4 = aot::mul(t3, t2);
            uint256_t const t5 = t4 ^ t1;
            uint256_t const t6 = aot::mload_c<traits, 256u, 288u, 27>(ctx, gas);
            uint256_t const t7 = aot::mul(t6, uint256_t{0x5af3107a4000ull});
            uint256_t const t8 = aot::udiv(t7, uint256_t{0x5af3107a4000ull});
            uint256_t const t9 = t8 ^ t6;
            bool const j25 = aot::nonzero(t9);
            top[1] = t5;
            top[2] = t6;
            top[3] = t7;
            top += 3;
            if (j25) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1ae1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ae1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x10, 0x15, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(s0 < s2);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j5 = aot::nonzero(t2);
            top += -3;
            if (j5) { MONAD_AOT_TAIL return b_1b76<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1ae9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ae9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x90}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x90}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x2ull};
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_1aee<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1aee(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x60, 0x1b, 0x60, 0x01, 0x51, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x60, 0x1b, 0x60, 0x01, 0x51, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const t2 = uint256_t{0x60ull} + t1;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            aot::mstore_c<traits, 576u, 608u, 57>(ctx, gas, t3);
            uint256_t const t4 = aot::mload_c<traits, 576u, 608u, 57>(ctx, gas);
            uint256_t const t5 = aot::mul(t4, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t6 = aot::udiv(t5, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t7 = t6 ^ t4;
            bool const j20 = aot::nonzero(t7);
            top[1] = t4;
            top[2] = t5;
            top += 2;
            if (j20) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1b1b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b1b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1b26<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b26(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x66, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x66, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 608u, 640u, 60>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 608u, 640u, 60>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t2 < uint256_t{0x11c37937e08000ull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j15 = aot::nonzero(t4);
            top += -2;
            if (j15) { MONAD_AOT_TAIL return b_1b49<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1b43<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b43(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_1b5a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1b49(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x68, 0x61, 0x51, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x68, 0x61, 0x51, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 608u, 640u, 60>(ctx, gas);
            uint256_t const t2 = aot::from_bool(uint256_t{0xb5e3af16b1880000ull, 0x2ull, 0x0ull, 0x0ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_1b5a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1b5a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1b60<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b60(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x01, 0x81, 0x81, 0x18, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x01, 0x81, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x1ull} + s0;
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 ^ s1;
            bool const j6 = aot::nonzero(t2);
            top[0] = t1;
            if (j6) { MONAD_AOT_TAIL return b_1aee<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1b6a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b6a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x60, 0x60, 0x61, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x60, 0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-3] = uint256_t{0x20ull};
            top[-2] = uint256_t{0xc0ull};
            top += -2;
            MONAD_AOT_TAIL return b_1be6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1b76(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x01, 0x81, 0x81, 0x18, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x01, 0x81, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x1ull} + s0;
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 ^ s1;
            bool const j7 = aot::nonzero(t2);
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_1735<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1b81<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b81(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x60, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x60, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x60, 0xfd}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x60, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x60, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x60, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 288u, 320u, 30>(ctx, gas, uint256_t{0x10ull});
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, uint256_t{0x0ull, 0x0ull, 0x636f6e7665726765ull, 0x446964206e6f7420ull});
            uint256_t const t1 = aot::mload_c<traits, 288u, 320u, 30>(ctx, gas);
            uint256_t const t2 = uint256_t{0x140ull} + t1;
            uint256_t const t3 = uint256_t{0x0ull} - t1;
            uint256_t const t4 = t3 & uint256_t{0x1full};
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t2, &t5, &t4);
            gas = ctx->gas_remaining;
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, uint256_t{0x8c379a0ull});
            aot::mstore_c<traits, 256u, 288u, 27>(ctx, gas, uint256_t{0x20ull});
            uint256_t const t6 = aot::mload_c<traits, 288u, 320u, 30>(ctx, gas);
            uint256_t const t7 = t6 + uint256_t{0x1full};
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t9 = uint256_t{0x44ull} + t8;
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0xfcull}, t9);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1be6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0xf3}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            aot::finish(ctx, gas, StatusCode::Success, s0, s1);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1be8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0x7e0e395eull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1e7c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1bf4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1bf4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x34, 0x17, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x34, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xa4ull});
            uint256_t const t3 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t4 = t3 | t2;
            bool const j6 = aot::nonzero(t4);
            if (j6) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1bfe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1bfe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x67, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x67, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x16345785d8a0000ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_1c16<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1c10<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c10(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_1c2b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1c16(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x6d, 0x60, 0x35, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x6d, 0x60, 0x35, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0x38c15b0a00000000ull, 0x314dc6448d93ull, 0x0ull, 0x0ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_1c2b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1c2b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1c31<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c31(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x60, 0x35, 0x60, 0x35, 0x80, 0x60, 0x1b, 0x81, 0x81, 0x60, 0x1c, 0x18, 0x61, 0x57}, 0, 7));
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x60, 0x35, 0x60, 0x35, 0x80, 0x60, 0x1b, 0x81, 0x81, 0x60, 0x1c, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t4 = aot::shl_c<2>(t3);
            uint256_t const t5 = aot::shr_c<2>(t4);
            uint256_t const t6 = t5 ^ t3;
            bool const j15 = aot::nonzero(t6);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top[4] = t4;
            top += 4;
            if (j15) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1c48<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c48(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x35, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x35, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::mul(s0, t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t4 = aot::udiv(t2, t1);
            uint256_t const t5 = aot::from_bool(t4 == s0);
            uint256_t const t6 = t5 | t3;
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            bool const j17 = aot::nonzero(t7);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            top[1] = t2;
            top += 1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1c5d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c5d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x6e, 0x81, 0x02, 0x81, 0x6e, 0x82, 0x04, 0x18, 0x61, 0x57}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x6e, 0x81, 0x02, 0x81, 0x6e, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mul(t1, uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull});
            uint256_t const t3 = aot::udiv(t2, uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull});
            uint256_t const t4 = t3 ^ t1;
            bool const j14 = aot::nonzero(t4);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j14) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1c8c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c8c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x04, 0x60, 0x52, 0x6e, 0x6e, 0x60, 0x51, 0x80, 0x60, 0x1b, 0x81, 0x81, 0x60, 0x1c, 0x18, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x04, 0x60, 0x52, 0x6e, 0x6e, 0x60, 0x51, 0x80, 0x60, 0x1b, 0x81, 0x81, 0x60, 0x1c, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::udiv(s0, s2);
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t3 = aot::shl_c<1>(t2);
            uint256_t const t4 = aot::shr_c<1>(t3);
            uint256_t const t5 = t4 ^ t2;
            bool const j18 = aot::nonzero(t5);
            top[-2] = uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull};
            top[-1] = uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull};
            top[0] = t2;
            top[1] = t3;
            top += 1;
            if (j18) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1cc3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1cc3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::mul(s0, t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t4 = aot::udiv(t2, t1);
            uint256_t const t5 = aot::from_bool(t4 == s0);
            uint256_t const t6 = t5 | t3;
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            bool const j17 = aot::nonzero(t7);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            top[1] = t2;
            top += 1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1cd8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1cd8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::udiv(t3, t2);
            uint256_t const t6 = aot::from_bool(t5 == t1);
            uint256_t const t7 = t6 | t4;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j20 = aot::nonzero(t8);
            top[-3] = t1;
            top[-2] = t2;
            top[-1] = t3;
            top += -1;
            if (j20) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1cf0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1cf0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x67, 0x60, 0x35, 0x01, 0x0a, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x67, 0x60, 0x35, 0x01, 0x0a, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t3 = t2 + uint256_t{0xde0b6b3a7640000ull};
            uint256_t const t4 = aot::exp_c<0x2u>(t3);
            uint256_t const t5 = t1 + t4;
            uint256_t const t6 = aot::from_bool(t5 < t1);
            bool const j18 = aot::nonzero(t6);
            top[-3] = t1;
            top[-2] = t4;
            top[-1] = t5;
            top += -1;
            if (j18) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1d0f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d0f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x67, 0x6e, 0x60, 0x60, 0x51, 0x0a, 0x04, 0x67, 0x60, 0x35, 0x60, 0x1b, 0x01, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 3, 6));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x67, 0x6e, 0x60, 0x60, 0x51, 0x0a, 0x04, 0x67, 0x60, 0x35, 0x60, 0x1b, 0x01, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::exp_c<0x2u>(t1);
            uint256_t const t3 = aot::udiv(t2, uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull});
            uint256_t const t4 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t5 = aot::shl_c<1>(t4);
            uint256_t const t6 = t5 + uint256_t{0x29a2241af62c0000ull};
            uint256_t const t7 = aot::mul(t3, t6);
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t9 = aot::udiv(t7, t6);
            uint256_t const t10 = aot::from_bool(t9 == t3);
            uint256_t const t11 = t10 | t8;
            uint256_t const t12 = aot::from_bool(!aot::nonzero(t11));
            bool const j30 = aot::nonzero(t12);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = uint256_t{0xde0b6b3a7640000ull};
            top[0] = t3;
            top[1] = t6;
            top[2] = t7;
            top += 2;
            if (j30) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1d53<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d53(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = s4 - t1;
            uint256_t const t3 = aot::from_bool(s4 < t2);
            bool const j12 = aot::nonzero(t3);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j12) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1d62<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d62(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x52, 0x61, 0x60, 0x60, 0x35, 0x0a, 0x60, 0x35, 0x02, 0x04, 0x60, 0x52, 0x60, 0x51, 0x6e, 0x60, 0x35, 0x60, 0x51, 0x60, 0x35, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 3, 7));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x52, 0x61, 0x60, 0x60, 0x35, 0x0a, 0x60, 0x35, 0x02, 0x04, 0x60, 0x52, 0x60, 0x51, 0x6e, 0x60, 0x35, 0x60, 0x51, 0x60, 0x35, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t2 = aot::exp_c<0x2u>(t1);
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const t4 = aot::mul(t3, t2);
            uint256_t const t5 = aot::udiv(t4, uint256_t{0x2710ull});
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t5);
            uint256_t const t6 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t7 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t8 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t9 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t10 = aot::mul(t8, t9);
            uint256_t const t11 = aot::from_bool(!aot::nonzero(t9));
            uint256_t const t12 = aot::udiv(t10, t9);
            uint256_t const t13 = aot::from_bool(t12 == t8);
            uint256_t const t14 = t13 | t11;
            uint256_t const t15 = aot::from_bool(!aot::nonzero(t14));
            bool const j39 = aot::nonzero(t15);
            top[-2] = t6;
            top[-1] = uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull};
            top[0] = t7;
            top[1] = t8;
            top[2] = t9;
            top[3] = t10;
            top += 3;
            if (j39) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1da6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1da6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::udiv(t3, t2);
            uint256_t const t6 = aot::from_bool(t5 == t1);
            uint256_t const t7 = t6 | t4;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j20 = aot::nonzero(t8);
            top[-3] = t1;
            top[-2] = t2;
            top[-1] = t3;
            top += -1;
            if (j20) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1dbe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dbe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = s4 + t1;
            uint256_t const t3 = aot::from_bool(t2 < s4);
            bool const j12 = aot::nonzero(t3);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j12) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1dcd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dcd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x52, 0x60, 0x51, 0x60, 0x35, 0x60, 0x51, 0x6e, 0x60, 0x35, 0x60, 0x51, 0x60, 0x35, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 3, 9));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x52, 0x60, 0x51, 0x60, 0x35, 0x60, 0x51, 0x6e, 0x60, 0x35, 0x60, 0x51, 0x60, 0x35, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t3 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t4 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t5 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t6 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t7 = aot::mul(t5, t6);
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t9 = aot::udiv(t7, t6);
            uint256_t const t10 = aot::from_bool(t9 == t5);
            uint256_t const t11 = t10 | t8;
            uint256_t const t12 = aot::from_bool(!aot::nonzero(t11));
            bool const j32 = aot::nonzero(t12);
            top[-2] = t1;
            top[-1] = t2;
            top[0] = t3;
            top[1] = uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull};
            top[2] = t4;
            top[3] = t5;
            top[4] = t6;
            top[5] = t7;
            top += 5;
            if (j32) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1e06<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e06(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::udiv(t3, t2);
            uint256_t const t6 = aot::from_bool(t5 == t1);
            uint256_t const t7 = t6 | t4;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j20 = aot::nonzero(t8);
            top[-3] = t1;
            top[-2] = t2;
            top[-1] = t3;
            top += -1;
            if (j20) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1e1e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e1e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = s4 + t1;
            uint256_t const t3 = aot::from_bool(t2 < s4);
            bool const j12 = aot::nonzero(t3);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j12) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1e2d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e2d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(s3, s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const t3 = aot::udiv(t1, s0);
            uint256_t const t4 = aot::from_bool(t3 == s3);
            uint256_t const t5 = t4 | t2;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j17 = aot::nonzero(t6);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j17) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1e41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e41(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x35, 0x80, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x35, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1e4e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e4e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            uint256_t const t2 = aot::mul(t1, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t3 = aot::udiv(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = t3 ^ t1;
            bool const j16 = aot::nonzero(t4);
            top[-1] = t1;
            top[0] = t2;
            if (j16) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1e71<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e71(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x04, 0x60, 0x52, 0x60, 0x60, 0xf3}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x04, 0x60, 0x52, 0x60, 0x60, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::udiv(s0, s2);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t1);
            aot::finish(ctx, gas, StatusCode::Success, uint256_t{0xc0ull}, uint256_t{0x20ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1e7c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1e82(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x52, 0x60, 0x60, 0x52, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x52, 0x60, 0x60, 0x52, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t1);
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t2 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t3 = aot::shr_c<128>(t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j14 = aot::nonzero(t4);
            if (j14) { MONAD_AOT_TAIL return b_1ea7<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1e99<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e99(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::shr_c<128>(t1);
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t2);
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, uint256_t{0x80ull});
            MONAD_AOT_TAIL return b_1ea7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ea7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<64>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_1ec5<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1eb3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1eb3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x51, 0x01, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x51, 0x01, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<64>(t1);
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t2);
            uint256_t const t3 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t4 = t3 + uint256_t{0x40ull};
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_1ec5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ec5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<32>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_1ee3<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1ed1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ed1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x51, 0x01, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x51, 0x01, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<32>(t1);
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t2);
            uint256_t const t3 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t4 = t3 + uint256_t{0x20ull};
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_1ee3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ee3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<16>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_1f01<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1eef<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1eef(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x51, 0x01, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x51, 0x01, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<16>(t1);
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t2);
            uint256_t const t3 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t4 = t3 + uint256_t{0x10ull};
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_1f01<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f01(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<8>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_1f1f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1f0d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f0d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x51, 0x01, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x51, 0x01, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<8>(t1);
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t2);
            uint256_t const t3 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t4 = t3 + uint256_t{0x8ull};
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_1f1f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f1f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<4>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_1f3d<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1f2b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f2b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x51, 0x01, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x51, 0x01, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<4>(t1);
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t2);
            uint256_t const t3 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t4 = t3 + uint256_t{0x4ull};
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_1f3d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f3d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<2>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_1f5b<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1f49<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f49(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x51, 0x01, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x51, 0x01, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<2>(t1);
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t2);
            uint256_t const t3 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t4 = t3 + uint256_t{0x2ull};
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_1f5b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f5b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<1>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_1f70<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1f67<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f67(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x51, 0x01, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x51, 0x01, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x1ull};
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_1f70<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f70(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_1f7e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1f78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f78(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_1f89<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f7e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x60, 0x51, 0x1b, 0x10}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x60, 0x51, 0x1b, 0x10}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t3 = aot::shl(t2, uint256_t{0x1ull});
            uint256_t const t4 = aot::from_bool(t3 < t1);
            top[1] = t4;
            top += 1;
            MONAD_AOT_TAIL return b_1f89<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f89(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_1f98<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1f8f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f8f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x51, 0x01, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x51, 0x01, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x1ull};
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_1f98<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f98(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x81, 0x52, 0x50, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x81, 0x52, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, t1);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 10137)) {
                MONAD_AOT_TAIL return jump_table<traits>[jt](ctx, bottom, top, gas);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1fa0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x52, 0x78, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x52, 0x78, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x4d542c5db2340000ull, 0x5fe645cc4873f9e6ull, 0x725dd1d243aba0e7ull, 0x12ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j10 = aot::nonzero(t3);
            if (j10) { MONAD_AOT_TAIL return b_2015<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1fc9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fc9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x71, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x71, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xca17a3aba173d3d5ull, 0x484932d2e725a5bbull, 0x154ull, 0x0ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_2000<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1fe5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fe5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x6e, 0x60, 0x51, 0x02, 0x60, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x6e, 0x60, 0x51, 0x02, 0x60, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull});
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_201c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2000(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x60, 0x51, 0x02, 0x60, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x60, 0x51, 0x02, 0x60, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0xde0b6b3a7640000ull});
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_201c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2015(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t1);
            MONAD_AOT_TAIL return b_201c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_201c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x52, 0x60, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x52, 0x60, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t1);
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, uint256_t{0x0ull});
            top[1] = uint256_t{0x2032ull};
            top[2] = uint256_t{0x120ull};
            top += 2;
            MONAD_AOT_TAIL return b_1e82<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2032(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 288u, 320u, 30>(ctx, gas);
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_203f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_203f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x12, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 256u, 288u, 27>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 256u, 288u, 27>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            bool const j8 = aot::nonzero(t2);
            top[0] = t1;
            if (j8) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_204f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_204f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x06, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x0a, 0x61, 0x51, 0x61, 0x0a, 0x60, 0x61, 0x51, 0x60, 0x81, 0x12, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x06, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x0a, 0x61, 0x51, 0x61, 0x0a, 0x60, 0x61, 0x51, 0x60, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::umod(s0, uint256_t{0x3ull});
            aot::mstore_c<traits, 288u, 320u, 30>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 288u, 320u, 30>(ctx, gas);
            auto const e10 = aot::exp<traits>(ctx, gas, uint256_t{0x3e8ull}, t2);
            gas = ctx->gas_remaining;
            uint256_t const t3 = aot::mload_c<traits, 288u, 320u, 30>(ctx, gas);
            auto const e14 = aot::exp<traits>(ctx, gas, uint256_t{0x4ecull}, t3);
            gas = ctx->gas_remaining;
            uint256_t const t4 = aot::mload_c<traits, 256u, 288u, 27>(ctx, gas);
            uint256_t const t5 = aot::from_bool(slt(t4, uint256_t{0x0ull}));
            bool const j22 = aot::nonzero(t5);
            top[0] = e10;
            top[1] = e14;
            top[2] = uint256_t{0x3ull};
            top[3] = t4;
            top += 3;
            if (j22) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2077<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2077(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x04, 0x60, 0x0a, 0x02, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x78, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x04, 0x60, 0x0a, 0x02, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x02, 0x60, 0x51, 0x04, 0x61, 0x51, 0x60, 0x1b, 0x01, 0x04, 0x61, 0x52, 0x78, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::udiv(s0, s1);
            auto const e2 = aot::exp<traits>(ctx, gas, uint256_t{0x2ull}, t1);
            gas = ctx->gas_remaining;
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = aot::mul(e2, s2);
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = aot::udiv(t2, s3);
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t3);
            uint256_t const t4 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t5 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t6 = aot::mul(t5, t4);
            uint256_t const t7 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t8 = aot::udiv(t7, t6);
            uint256_t const t9 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t10 = aot::shl_c<1>(t9);
            uint256_t const t11 = t10 + t8;
            uint256_t const t12 = aot::udiv(t11, uint256_t{0x3ull});
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t12);
            uint256_t const t13 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t14 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t15 = aot::mul(t14, t13);
            uint256_t const t16 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t17 = aot::udiv(t16, t15);
            uint256_t const t18 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t19 = aot::shl_c<1>(t18);
            uint256_t const t20 = t19 + t17;
            uint256_t const t21 = aot::udiv(t20, uint256_t{0x3ull});
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t21);
            uint256_t const t22 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t23 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t24 = aot::mul(t23, t22);
            uint256_t const t25 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t26 = aot::udiv(t25, t24);
            uint256_t const t27 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t28 = aot::shl_c<1>(t27);
            uint256_t const t29 = t28 + t26;
            uint256_t const t30 = aot::udiv(t29, uint256_t{0x3ull});
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t30);
            uint256_t const t31 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t32 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t33 = aot::mul(t32, t31);
            uint256_t const t34 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t35 = aot::udiv(t34, t33);
            uint256_t const t36 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t37 = aot::shl_c<1>(t36);
            uint256_t const t38 = t37 + t35;
            uint256_t const t39 = aot::udiv(t38, uint256_t{0x3ull});
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t39);
            uint256_t const t40 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t41 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t42 = aot::mul(t41, t40);
            uint256_t const t43 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t44 = aot::udiv(t43, t42);
            uint256_t const t45 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t46 = aot::shl_c<1>(t45);
            uint256_t const t47 = t46 + t44;
            uint256_t const t48 = aot::udiv(t47, uint256_t{0x3ull});
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t48);
            uint256_t const t49 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t50 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t51 = aot::mul(t50, t49);
            uint256_t const t52 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t53 = aot::udiv(t52, t51);
            uint256_t const t54 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t55 = aot::shl_c<1>(t54);
            uint256_t const t56 = t55 + t53;
            uint256_t const t57 = aot::udiv(t56, uint256_t{0x3ull});
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t57);
            uint256_t const t58 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t59 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t60 = aot::mul(t59, t58);
            uint256_t const t61 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t62 = aot::udiv(t61, t60);
            uint256_t const t63 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t64 = aot::shl_c<1>(t63);
            uint256_t const t65 = t64 + t62;
            uint256_t const t66 = aot::udiv(t65, uint256_t{0x3ull});
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t66);
            uint256_t const t67 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t68 = aot::from_bool(t67 < uint256_t{0x4d542c5db2340000ull, 0x5fe645cc4873f9e6ull, 0x725dd1d243aba0e7ull, 0x12ull});
            uint256_t const t69 = aot::from_bool(!aot::nonzero(t68));
            bool const j132 = aot::nonzero(t69);
            top += -4;
            if (j132) { MONAD_AOT_TAIL return b_2194<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2168<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2168(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x71, 0x60, 0x51, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x71, 0x60, 0x51, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xca17a3aba173d3d5ull, 0x484932d2e725a5bbull, 0x154ull, 0x0ull});
            bool const j5 = aot::nonzero(t2);
            if (j5) { MONAD_AOT_TAIL return b_21a4<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2183<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2183(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x62, 0x61, 0x51, 0x02, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x62, 0x61, 0x51, 0x02, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0xf4240ull});
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_21a4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2194(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x64, 0x61, 0x51, 0x02, 0x61, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x64, 0x61, 0x51, 0x02, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0xe8d4a51000ull});
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_21a4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_21a4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x81, 0x52, 0x50, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x81, 0x52, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, t1);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 10137)) {
                MONAD_AOT_TAIL return jump_table<traits>[jt](ctx, bottom, top, gas);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_21ad(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x80, 0x60, 0x03, 0x60, 0x81, 0x11, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x80, 0x60, 0x03, 0x60, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t2 = uint256_t{0x1ull} - t1;
            uint256_t const t3 = aot::from_bool(uint256_t{0x1ull} < t2);
            bool const j10 = aot::nonzero(t3);
            top[1] = t1;
            top[2] = t2;
            top += 2;
            if (j10) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_21bd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21bd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x81, 0x11, 0x61, 0x57}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x1ull} < s0);
            bool const j6 = aot::nonzero(t1);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (j6) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_21c7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21c7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1b, 0x60, 0x01, 0x51, 0x61, 0x52, 0x60, 0x51, 0x6f, 0x81, 0x11, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1b, 0x60, 0x01, 0x51, 0x61, 0x52, 0x60, 0x51, 0x6f, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const t2 = uint256_t{0x80ull} + t1;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            aot::mstore_c<traits, 288u, 320u, 30>(ctx, gas, t3);
            uint256_t const t4 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t5 = aot::from_bool(uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull} < t4);
            bool const j13 = aot::nonzero(t5);
            top[0] = t4;
            if (j13) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_21ec<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21ec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x61, 0x51, 0x80, 0x60, 0x1b, 0x81, 0x81, 0x60, 0x1c, 0x18, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x61, 0x51, 0x80, 0x60, 0x1b, 0x81, 0x81, 0x60, 0x1c, 0x18, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::exp_c<0x2u>(s0);
            uint256_t const t2 = aot::mload_c<traits, 288u, 320u, 30>(ctx, gas);
            uint256_t const t3 = aot::shl_c<2>(t2);
            uint256_t const t4 = aot::shr_c<2>(t3);
            uint256_t const t5 = t4 ^ t2;
            bool const j16 = aot::nonzero(t5);
            top[0] = t1;
            top[1] = t2;
            top[2] = t3;
            top += 2;
            if (j16) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2204<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2204(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x80, 0x15, 0x61, 0x57}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j5 = aot::nonzero(t1);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (j5) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_220c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_220c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 288u, 320u, 30>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0x1bc16d674ec80000ull});
            uint256_t const t4 = aot::udiv(t3, uint256_t{0x1bc16d674ec80000ull});
            uint256_t const t5 = t4 ^ t2;
            bool const j20 = aot::nonzero(t5);
            top[-1] = t2;
            top[0] = t3;
            if (j20) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2237<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2237(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2242<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2242(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x6e, 0x04, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x6e, 0x04, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 352u, 384u, 36>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 256u, 288u, 27>(ctx, gas);
            uint256_t const t3 = aot::udiv(uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull}, t2);
            uint256_t const t4 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t5 = aot::from_bool(t4 < t3);
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j18 = aot::nonzero(t6);
            top += -2;
            if (j18) { MONAD_AOT_TAIL return b_2272<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_226c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_226c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_227d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2272(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 256u, 288u, 27>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t1 < t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            top[1] = t4;
            top += 1;
            MONAD_AOT_TAIL return b_227d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_227d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2283<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2283(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x65, 0x81, 0x04, 0x90, 0x50, 0x60, 0x51, 0x65, 0x81, 0x04, 0x90, 0x50, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x11, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x60, 0x81, 0x81, 0x18, 0x60, 0x83, 0x11, 0x02, 0x18, 0x90, 0x50, 0x61, 0x52, 0x60, 0x60, 0x90}, 0, 6));
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x65, 0x81, 0x04, 0x90, 0x50, 0x60, 0x51, 0x65, 0x81, 0x04, 0x90, 0x50, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x11, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x60, 0x81, 0x81, 0x18, 0x60, 0x83, 0x11, 0x02, 0x18, 0x90, 0x50, 0x61, 0x52, 0x60, 0x60, 0x90}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 288u, 320u, 30>(ctx, gas);
            uint256_t const t2 = aot::udiv(t1, uint256_t{0x5af3107a4000ull});
            uint256_t const t3 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t4 = aot::udiv(t3, uint256_t{0x5af3107a4000ull});
            uint256_t const t5 = t4 ^ t2;
            uint256_t const t6 = aot::from_bool(t4 < t2);
            uint256_t const t7 = aot::mul(t6, t5);
            uint256_t const t8 = t7 ^ t4;
            uint256_t const t9 = uint256_t{0x64ull} ^ t8;
            uint256_t const t10 = aot::from_bool(uint256_t{0x64ull} < t8);
            uint256_t const t11 = aot::mul(t10, t9);
            uint256_t const t12 = t11 ^ uint256_t{0x64ull};
            aot::mstore_c<traits, 384u, 416u, 39>(ctx, gas, t12);
            top[1] = uint256_t{0xffull};
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_22c3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_22c3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 1, 7));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 416u, 448u, 42>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            aot::mstore_c<traits, 448u, 480u, 45>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t4 = aot::mul(t2, t3);
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t6 = aot::udiv(t4, t3);
            uint256_t const t7 = aot::from_bool(t6 == t2);
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            bool const j25 = aot::nonzero(t9);
            top[1] = t2;
            top[2] = t3;
            top[3] = t4;
            top += 3;
            if (j25) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_22e9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_22e9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x60, 0x1b, 0x81, 0x81, 0x60, 0x1c, 0x18, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x60, 0x1b, 0x81, 0x81, 0x60, 0x1c, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<1>(s0);
            uint256_t const t2 = aot::shr_c<1>(t1);
            uint256_t const t3 = t2 ^ s0;
            bool const j13 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j13) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_22fb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_22fb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2306<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2306(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 480u, 512u, 48>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 288u, 320u, 30>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t4 = t2 + t3;
            uint256_t const t5 = aot::from_bool(t4 < t2);
            bool const j20 = aot::nonzero(t5);
            top[-1] = t2;
            top[0] = t3;
            top[1] = t4;
            top += 1;
            if (j20) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2323<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2323(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x51, 0x67, 0x81, 0x01, 0x81, 0x81, 0x10, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x51, 0x67, 0x81, 0x01, 0x81, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 512u, 544u, 51>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0xde0b6b3a7640000ull};
            uint256_t const t3 = aot::from_bool(t2 < t1);
            bool const j15 = aot::nonzero(t3);
            top[-2] = t1;
            top[-1] = t2;
            top += -1;
            if (j15) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2340<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2340(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 544u, 576u, 54>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 480u, 512u, 48>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t1 < t2);
            bool const j10 = aot::nonzero(t3);
            top += -2;
            if (j10) { MONAD_AOT_TAIL return b_237e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2353<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2353(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 480u, 512u, 48>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t3 = t1 - t2;
            uint256_t const t4 = aot::from_bool(t1 < t3);
            bool const j11 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j11) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2365<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2365(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x81, 0x01, 0x81, 0x81, 0x10, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x81, 0x01, 0x81, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x1ull};
            uint256_t const t2 = aot::from_bool(t1 < s0);
            bool const j11 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j11) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2374<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2374(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x52, 0x61, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 544u, 576u, 54>(ctx, gas, s0);
            top += -2;
            MONAD_AOT_TAIL return b_23a6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_237e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 480u, 512u, 48>(ctx, gas);
            uint256_t const t3 = t1 - t2;
            uint256_t const t4 = aot::from_bool(t1 < t3);
            bool const j12 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j12) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2391<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2391(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x81, 0x01, 0x81, 0x81, 0x10, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x81, 0x01, 0x81, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x1ull};
            uint256_t const t2 = aot::from_bool(t1 < s0);
            bool const j11 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j11) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_23a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_23a0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x52}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 544u, 576u, 54>(ctx, gas, s0);
            top += -2;
            MONAD_AOT_TAIL return b_23a6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_23a6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t3 = aot::udiv(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = t3 ^ t1;
            bool const j12 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top += 2;
            if (j12) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_23c6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_23c6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_23d1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_23d1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            uint256_t const t2 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::udiv(t3, t2);
            uint256_t const t6 = aot::from_bool(t5 == t1);
            uint256_t const t7 = t6 | t4;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j22 = aot::nonzero(t8);
            top[-1] = t1;
            top[0] = t2;
            top[1] = t3;
            top += 1;
            if (j22) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_23ec<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_23ec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x51, 0x80, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_23f9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_23f9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            uint256_t const t2 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::udiv(t3, t2);
            uint256_t const t6 = aot::from_bool(t5 == t1);
            uint256_t const t7 = t6 | t4;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j22 = aot::nonzero(t8);
            top[-1] = t1;
            top[0] = t2;
            top[1] = t3;
            top += 1;
            if (j22) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2414<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2414(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x81, 0x02, 0x81, 0x61, 0x82, 0x04, 0x18, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x81, 0x02, 0x81, 0x61, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(s0, uint256_t{0x2710ull});
            uint256_t const t2 = aot::udiv(t1, uint256_t{0x2710ull});
            uint256_t const t3 = t2 ^ s0;
            bool const j13 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j13) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2428<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2428(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2433<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2433(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 576u, 608u, 57>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 480u, 512u, 48>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0x1bc16d674ec80000ull});
            uint256_t const t4 = aot::udiv(t3, uint256_t{0x1bc16d674ec80000ull});
            uint256_t const t5 = t4 ^ t2;
            bool const j20 = aot::nonzero(t5);
            top[-1] = t2;
            top[0] = t3;
            if (j20) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_245e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_245e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_246a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_246a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x80, 0x67, 0x01, 0x67, 0x81, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x80, 0x67, 0x01, 0x67, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            uint256_t const t2 = uint256_t{0xde0b6b3a7640000ull} + t1;
            uint256_t const t3 = aot::from_bool(t2 < uint256_t{0xde0b6b3a7640000ull});
            bool const j14 = aot::nonzero(t3);
            top[-1] = t1;
            top[0] = t2;
            if (j14) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_248b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_248b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 608u, 640u, 60>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t3 = aot::udiv(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = t3 ^ t1;
            bool const j15 = aot::nonzero(t4);
            top[-1] = t1;
            top[0] = t2;
            if (j15) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_24b1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_24b1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 512u, 544u, 51>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 608u, 640u, 60>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::udiv(t3, t2);
            uint256_t const t6 = aot::from_bool(t5 == t1);
            uint256_t const t7 = t6 | t4;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j19 = aot::nonzero(t8);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            top[1] = t2;
            top[2] = t3;
            top += 2;
            if (j19) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_24cb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_24cb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s3 + s0;
            uint256_t const t2 = aot::from_bool(t1 < s3);
            bool const j11 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j11) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_24d9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_24d9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 576u, 608u, 57>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 + t1;
            uint256_t const t3 = aot::from_bool(t2 < s0);
            bool const j13 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = t2;
            if (j13) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_24eb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_24eb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 640u, 672u, 63>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 608u, 640u, 60>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::udiv(t3, t2);
            uint256_t const t6 = aot::from_bool(t5 == t1);
            uint256_t const t7 = t6 | t4;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j23 = aot::nonzero(t8);
            top[-2] = t1;
            top[-1] = t2;
            top[0] = t3;
            if (j23) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_250a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_250a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x10, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 672u, 704u, 66>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 640u, 672u, 63>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t2 < t1);
            bool const j12 = aot::nonzero(t3);
            top += -3;
            if (j12) { MONAD_AOT_TAIL return b_253d<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_251f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_251f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 640u, 672u, 63>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t3 = t1 - t2;
            uint256_t const t4 = aot::from_bool(t1 < t3);
            bool const j11 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j11) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2531<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2531(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 640u, 672u, 63>(ctx, gas, s0);
            top += -3;
            MONAD_AOT_TAIL return b_2550<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_253d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t2 = aot::shr_c<1>(t1);
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_2714<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2550(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 640u, 672u, 63>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j8 = aot::nonzero(t3);
            top[1] = t1;
            top[2] = t2;
            top += 2;
            if (j8) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_255f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_255f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 704u, 736u, 70>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 576u, 608u, 57>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j16 = aot::nonzero(t4);
            top[-1] = t2;
            top[0] = t3;
            if (j16) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2578<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2578(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 736u, 768u, 73>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 640u, 672u, 63>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t4 = aot::mul(t3, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t5 = aot::udiv(t4, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t6 = t5 ^ t3;
            bool const j22 = aot::nonzero(t6);
            top[-1] = t2;
            top[0] = t3;
            top[1] = t4;
            top += 1;
            if (j22) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_25a6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_25a6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s2 + s0;
            uint256_t const t2 = aot::from_bool(t1 < s2);
            bool const j9 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j9) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_25b2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_25b2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_25c0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_25c0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            uint256_t const t2 = aot::mload_c<traits, 736u, 768u, 73>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = aot::udiv(t3, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t5 = t4 ^ t2;
            bool const j18 = aot::nonzero(t5);
            top[-1] = t1;
            top[0] = t2;
            top[1] = t3;
            top += 1;
            if (j18) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_25e7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_25e7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 480u, 512u, 48>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_25f3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_25f3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s2 + t1;
            uint256_t const t3 = aot::from_bool(t2 < s2);
            bool const j14 = aot::nonzero(t3);
            top[-1] = t1;
            top[0] = t2;
            if (j14) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2604<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2604(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 768u, 800u, 76>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 736u, 768u, 73>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 512u, 544u, 51>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = aot::udiv(t3, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t5 = t4 ^ t2;
            bool const j19 = aot::nonzero(t5);
            top[-2] = t1;
            top[-1] = t2;
            top[0] = t3;
            if (j19) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2630<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2630(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_263c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_263c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s2 + t1;
            uint256_t const t3 = aot::from_bool(t2 < s2);
            bool const j14 = aot::nonzero(t3);
            top[-1] = t1;
            top[0] = t2;
            if (j14) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_264d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_264d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x10, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 736u, 768u, 73>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 736u, 768u, 73>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 768u, 800u, 76>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t2 < t1);
            bool const j12 = aot::nonzero(t3);
            top += -3;
            if (j12) { MONAD_AOT_TAIL return b_2680<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2662<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2662(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 768u, 800u, 76>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 736u, 768u, 73>(ctx, gas);
            uint256_t const t3 = t1 - t2;
            uint256_t const t4 = aot::from_bool(t1 < t3);
            bool const j11 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j11) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2674<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2674(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, s0);
            top += -3;
            MONAD_AOT_TAIL return b_268f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2680(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x90, 0x50, 0x61, 0x52}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x90, 0x50, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t2 = aot::shr_c<1>(t1);
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_268f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_268f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 800u, 832u, 79>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t1 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t1 < t2);
            bool const j10 = aot::nonzero(t3);
            if (j10) { MONAD_AOT_TAIL return b_26c1<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_26a3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_26a3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t3 = t1 - t2;
            uint256_t const t4 = aot::from_bool(t1 < t3);
            bool const j11 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j11) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_26b5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_26b5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 800u, 832u, 79>(ctx, gas, s0);
            top += -3;
            MONAD_AOT_TAIL return b_26dc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_26c1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t3 = t1 - t2;
            uint256_t const t4 = aot::from_bool(t1 < t3);
            bool const j12 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j12) { MONAD_AOT_TAIL return b_2788<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_26d4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_26d4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 800u, 832u, 79>(ctx, gas, s0);
            top += -3;
            MONAD_AOT_TAIL return b_26dc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_26dc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x65, 0x81, 0x04, 0x90, 0x50, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x11, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}, 0, 6));
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x65, 0x81, 0x04, 0x90, 0x50, 0x80, 0x82, 0x81, 0x18, 0x82, 0x84, 0x11, 0x02, 0x18, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 384u, 416u, 39>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t3 = aot::udiv(t2, uint256_t{0x5af3107a4000ull});
            uint256_t const t4 = t3 ^ t1;
            uint256_t const t5 = aot::from_bool(t3 < t1);
            uint256_t const t6 = aot::mul(t5, t4);
            uint256_t const t7 = t6 ^ t3;
            uint256_t const t8 = aot::mload_c<traits, 800u, 832u, 79>(ctx, gas);
            uint256_t const t9 = aot::from_bool(t8 < t7);
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            bool const j28 = aot::nonzero(t10);
            if (j28) { MONAD_AOT_TAIL return b_2714<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2707<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2707(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x83, 0x52, 0x50, 0x50, 0x50, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x83, 0x52, 0x50, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, t1);
            top += -3;
            MONAD_AOT_TAIL return b_2786<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2714(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x01, 0x81, 0x81, 0x18, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x01, 0x81, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x1ull} + s0;
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 ^ s1;
            bool const j7 = aot::nonzero(t2);
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_22c3<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_271f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_271f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x60, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x60, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 416u, 448u, 42>(ctx, gas, uint256_t{0x10ull});
            aot::mstore_c<traits, 448u, 480u, 45>(ctx, gas, uint256_t{0x0ull, 0x0ull, 0x636f6e7665726765ull, 0x446964206e6f7420ull});
            uint256_t const t1 = aot::mload_c<traits, 416u, 448u, 42>(ctx, gas);
            uint256_t const t2 = uint256_t{0x1c0ull} + t1;
            uint256_t const t3 = uint256_t{0x0ull} - t1;
            uint256_t const t4 = t3 & uint256_t{0x1full};
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t2, &t5, &t4);
            gas = ctx->gas_remaining;
            aot::mstore_c<traits, 352u, 384u, 36>(ctx, gas, uint256_t{0x8c379a0ull});
            aot::mstore_c<traits, 384u, 416u, 39>(ctx, gas, uint256_t{0x20ull});
            uint256_t const t6 = aot::mload_c<traits, 416u, 448u, 42>(ctx, gas);
            uint256_t const t7 = t6 + uint256_t{0x1full};
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t9 = uint256_t{0x44ull} + t8;
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x17cull}, t9);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2786(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 10137)) {
                MONAD_AOT_TAIL return jump_table<traits>[jt](ctx, bottom, top, gas);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2788(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        void run(
            void *, Context *const ctx, interpreter::Intercode const *,
            uint256_t *const stack_ptr, void *)
        {
            b_0<traits>(ctx, stack_ptr - 1, stack_ptr - 1, ctx->gas_remaining);
        }
    }

    template void c_70d105ee0e9b8572::run<EvmTraits<MONAD_ETH_OSAKA>>(
        void *, Context *, interpreter::Intercode const *, uint256_t *, void *);
}
