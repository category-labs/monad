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

// Written by aotgen.py from the code whose keccak is 4031de700c2e5e41189dffb62c430bcaea2493c7ca522721634c3747647bea97: not to be edited.

#include <category/vm/aot/ops.hpp>
#include <category/vm/interpreter/execute.hpp>
#include <category/vm/interpreter/intercode.hpp>

#define MONAD_AOT_TAIL __attribute__((musttail))

namespace monad::vm::aot
{
    using runtime::Context;
    using runtime::StatusCode;

    // 10935 bytes, keccak 4031de700c2e5e41189dffb62c430bcaea2493c7ca522721634c3747647bea97
    namespace c_4031de700c2e5e41
    {
        template <Traits traits>
        using Block = void (*)(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        [[gnu::noinline]] void b_0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_17(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_22(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_95(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_cb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_da(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_df(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ed(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_105(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_10a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_11f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_125(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_12e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_140(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_16f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_17a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_197(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_19c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ad(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_216(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_221(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_231(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_241(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_24c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_25b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_266(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_271(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_27d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_28c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_29b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ca(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_35f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_374(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3e0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3f6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_44a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_47e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_48c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4a2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4b8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4e4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4f3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_4f6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_521(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_53f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_55b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_575(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_58e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_5a5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_5ba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_5ce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_5e3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_65d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_68f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_69e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_6a1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6d0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6df(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_6e2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6ea(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_71b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_72a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_72d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_746(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_75c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_7d1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_7e0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_826(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_859(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_88c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_895(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_8bf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_8e2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_900(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_918(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_964(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_978(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_99d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9b0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9f8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a42(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a56(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a7b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a8d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_aa6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_adf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_aeb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b07(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_b13(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b25(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_b31(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b3f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_b4b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b57(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_b63(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_bd3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_be7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c12(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c1b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c35(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c5c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c66(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c72(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c7f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c8c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c90(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ca2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_cb8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ce3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_cec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d09(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d30(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d3a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d51(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d5c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d6c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d79(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d7d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_db6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ddd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e12(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e20(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e36(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e48(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e5e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e9b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ec3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_eea(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_efe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f26(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f30(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f57(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f70(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f75(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f86(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f8b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fef(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ff5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ff7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1003(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_100b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1014(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1020(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1028(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_102f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1041(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1082(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_108b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10aa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_10cc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_10dc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10f7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_110c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1131(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_114a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_115d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_116c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1179(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11a1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11ba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11cd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11e1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_11f0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_122a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1243(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1256(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_126e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1286(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1293(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12f3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1307(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1318(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_13ba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_13df(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_13fb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1437(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1448(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1454(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1491(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14a2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_14aa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14b8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_14cc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_14da(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14e8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_14f9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1507(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1537(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_153b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1572(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1577(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1588(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_158d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_15f1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_15fc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1609(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1614(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_167a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_167c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1688(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1690(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_16a2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_16a7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_16bc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_16c2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_16dc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_16f1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1709(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1738(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_176f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1784(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_179c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_17bb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_17ff(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_180e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1852(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_186a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1879(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18b2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18ca(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18d9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18ed(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18fa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_191d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1955(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_196d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_197c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1990(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_199d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_19c0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_19cb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_19d7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_19df(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_19f6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a02(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a0a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a1e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a23(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a2f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a37(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a50(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a55(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a61(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a69(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a7b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a86(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1aac(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ab9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ac6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ada(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ae7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1afb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b30(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b3c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b60(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b6c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b89(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ba4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c13(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c5a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d0f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d19(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d3d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d53(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d5b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d78(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d8a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1da6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dbe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dd0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ddc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1df1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e25(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e37(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e43(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e60(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e7e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e91(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ea3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1eb2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ecf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ede(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f05(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f11(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f2c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f3a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f55(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f69(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f75(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fa0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fac(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fcd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ff3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_200d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_201b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_202d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_204d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2062(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2074(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_20a2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_20bb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_20ea(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_20f6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2104(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_212b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2137(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2148(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2174(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2180(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2191(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21a6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21b8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21e1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21f3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2212(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2245(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2265(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2271(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_228e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_22a9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2326(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_238e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_23a4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_23b2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_23be(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_23d0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_23dc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_23ee(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_23fa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_240c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2418(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_242a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2436(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2448(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2454(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2466(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2472(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_247b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2483(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2493(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2499(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_24a2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_24aa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_24d2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_24ee(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2525(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_253a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2547(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2556(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_257d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_266e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2689(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_26aa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_26b3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_26de(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_26f7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2708(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2710(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2722(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_272a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_272c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_273d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_274e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2774(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_277f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_279d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_27b2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_27ce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_27e3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_27f3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2812(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2829(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2838(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2842(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_284c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2854(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2884(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_288c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_28a0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_28fb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2aa0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2aa4(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        void bad(Context *const ctx, uint256_t const *, uint256_t *, int64_t)
        {
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        inline constexpr Block<traits> jump_table[10935] = {
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_95<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_ba<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_c5<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_df<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_ed<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_10a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_11f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_12e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_19c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1ad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_216<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_241<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_25b<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_271<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_4f6<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &b_5e3<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_65d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_6a1<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_6e2<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_72d<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_895<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_adf<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_b13<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_b31<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_b4b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_b63<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_c66<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_c7f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_c90<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_d3a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_d6c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_d7d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_f75<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_f86<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_fef<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_ff5<traits>,
            &bad<traits>, &b_ff7<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1014<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_102f<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1041<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_10cc<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_10dc<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_116c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1179<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_11f0<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &b_1286<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1293<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1307<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1318<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1454<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_14aa<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_14cc<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_14da<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_14f9<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1507<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_153b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1577<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1588<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_15f1<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1609<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_167a<traits>, &bad<traits>, &b_167c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_16a7<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_16bc<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_19cb<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_19f6<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1a1e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1a23<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1a50<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1a55<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1a7b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &b_1a86<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1ab9<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1ada<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1afb<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &b_238e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_23b2<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_23d0<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_23ee<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_240c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_242a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2448<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2466<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_247b<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2493<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_24a2<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_24aa<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2525<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_253a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_26aa<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_26b3<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2710<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2722<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_272a<traits>, &bad<traits>, &b_272c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_284c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2854<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_288c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_28fb<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2aa4<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>,
        };

        template <Traits traits>
        [[gnu::noinline]] void b_0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x11, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(uint256_t{0x3ull} < t1);
            bool const j4 = aot::nonzero(t2);
            if (j4) { MONAD_AOT_TAIL return b_c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a82);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x35, 0x60, 0x1c, 0x34, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x35, 0x60, 0x1c, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x0ull});
            uint256_t const t2 = aot::shr_c<224>(t1);
            uint256_t const t3 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j7 = aot::nonzero(t3);
            top[1] = t2;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_17<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_17(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0x54fd4d50ull};
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_95<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_22<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_22(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0x60, 0x52, 0x60, 0x60, 0x52, 0x7f, 0x60, 0x52, 0x60, 0x81, 0x60, 0x01, 0x81, 0x51, 0x60, 0x83, 0x01, 0x60, 0x83, 0x01, 0x81, 0x51, 0x81, 0x52, 0x50, 0x50, 0x80, 0x82, 0x52, 0x50, 0x80, 0x51, 0x80, 0x60, 0x83, 0x01, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x60, 0x19, 0x60, 0x82, 0x51, 0x60, 0x01, 0x01, 0x16, 0x90, 0x50, 0x90, 0x50, 0x81, 0x01, 0x90, 0x50, 0x60, 0xf3}, 0, 8));
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0x60, 0x52, 0x60, 0x60, 0x52, 0x7f, 0x60, 0x52, 0x60, 0x81, 0x60, 0x01, 0x81, 0x51, 0x60, 0x83, 0x01, 0x60, 0x83, 0x01, 0x81, 0x51, 0x81, 0x52, 0x50, 0x50, 0x80, 0x82, 0x52, 0x50, 0x80, 0x51, 0x80, 0x60, 0x83, 0x01, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x60, 0x19, 0x60, 0x82, 0x51, 0x60, 0x01, 0x01, 0x16, 0x90, 0x50, 0x90, 0x50, 0x81, 0x01, 0x90, 0x50, 0x60, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, uint256_t{0x20ull});
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, uint256_t{0x6ull});
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x76322e302e300000ull});
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t2);
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t1);
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
        [[gnu::noinline]] void b_95(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0x4a2ab3beull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_ff7<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_a1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xe4ull});
            bool const j4 = aot::nonzero(t2);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_a9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xa8cull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_ba<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_b5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_c5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x60, 0x35, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x60, 0x35, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0x1017df80ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_c5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_cb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_cb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x64, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x64, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x2540be400ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_df<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_da<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_da(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_ed<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_df(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x66, 0x60, 0x35, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x66, 0x60, 0x35, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xb1a2bc2ec50000ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_ed<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ed(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_f3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x67, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x67, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x16345785d8a0000ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_10a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_105<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_105(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_11f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_10a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x6d, 0x60, 0x35, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x6d, 0x60, 0x35, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0x38c15b0a00000000ull, 0x314dc6448d93ull, 0x0ull, 0x0ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_11f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_11f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_125<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_125(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x52, 0x5f, 0x60, 0x90}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x52, 0x5f, 0x60, 0x90}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1248u, 1280u, 123>(ctx, gas, uint256_t{0x0ull});
            top[1] = uint256_t{0x3ull};
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_12e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_12e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x52, 0x60, 0x35, 0x61, 0x51, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x52, 0x60, 0x35, 0x61, 0x51, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1280u, 1312u, 126>(ctx, gas, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xc4ull});
            uint256_t const t2 = aot::mload_c<traits, 1280u, 1312u, 126>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t2 == t1);
            bool const j10 = aot::nonzero(t3);
            if (j10) { MONAD_AOT_TAIL return b_216<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_140<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_140(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x60, 0x81, 0x11, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x60, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1280u, 1312u, 126>(ctx, gas);
            uint256_t const t2 = aot::from_bool(uint256_t{0x2ull} < t1);
            bool const j6 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_14c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1b, 0x60, 0x01, 0x35, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1b, 0x60, 0x01, 0x35, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const t2 = uint256_t{0x44ull} + t1;
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const t4 = aot::mul(t3, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t5 = aot::udiv(t4, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t6 = t5 ^ t3;
            bool const j14 = aot::nonzero(t6);
            top[0] = t3;
            top[1] = t4;
            top += 1;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_16f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_16f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x35, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x35, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_17a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_17a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x66, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x66, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 1248u, 1280u, 123>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 1248u, 1280u, 123>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t2 < uint256_t{0x2386f26fc10000ull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j15 = aot::nonzero(t4);
            top += -2;
            if (j15) { MONAD_AOT_TAIL return b_19c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_197<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_197(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_1ad<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_19c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x68, 0x61, 0x51, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x68, 0x61, 0x51, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1248u, 1280u, 123>(ctx, gas);
            uint256_t const t2 = aot::from_bool(uint256_t{0x6bc75e2d63100000ull, 0x5ull, 0x0ull, 0x0ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_1ad<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ad(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j2 = aot::nonzero(s0);
            top += -1;
            if (j2) { MONAD_AOT_TAIL return b_216<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1b2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1312u, 1344u, 129>(ctx, gas, uint256_t{0x12ull});
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, uint256_t{0x0ull, 0x695d000000000000ull, 0x616c75657320785bull, 0x556e736166652076ull});
            uint256_t const t1 = aot::mload_c<traits, 1312u, 1344u, 129>(ctx, gas);
            uint256_t const t2 = uint256_t{0x540ull} + t1;
            uint256_t const t3 = uint256_t{0x0ull} - t1;
            uint256_t const t4 = t3 & uint256_t{0x1full};
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t2, &t5, &t4);
            gas = ctx->gas_remaining;
            aot::mstore_c<traits, 1248u, 1280u, 123>(ctx, gas, uint256_t{0x8c379a0ull});
            aot::mstore_c<traits, 1280u, 1312u, 126>(ctx, gas, uint256_t{0x20ull});
            uint256_t const t6 = aot::mload_c<traits, 1312u, 1344u, 129>(ctx, gas);
            uint256_t const t7 = t6 + uint256_t{0x1full};
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t9 = uint256_t{0x44ull} + t8;
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x4fcull}, t9);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_216(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j7) { MONAD_AOT_TAIL return b_12e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_221<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_221(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x60, 0x36, 0x61, 0x37, 0x60, 0x35, 0x61, 0x57}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x60, 0x36, 0x61, 0x37, 0x60, 0x35, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const k5_0 = uint256_t{0x500ull};
            uint256_t const k5_2 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k5_0, &t1, &k5_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0xc4ull});
            bool const j9 = aot::nonzero(t2);
            top += -2;
            if (j9) { MONAD_AOT_TAIL return b_241<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_231<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_231(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x52, 0x60, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x52, 0x60, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1280u, 1312u, 126>(ctx, gas, uint256_t{0x1ull});
            aot::mstore_c<traits, 1312u, 1344u, 129>(ctx, gas, uint256_t{0x2ull});
            MONAD_AOT_TAIL return b_271<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_241(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x35, 0x18, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x35, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xc4ull});
            uint256_t const t2 = t1 ^ uint256_t{0x1ull};
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return b_25b<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_24c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_24c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x52, 0x60, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x52, 0x60, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1280u, 1312u, 126>(ctx, gas, uint256_t{0x0ull});
            aot::mstore_c<traits, 1312u, 1344u, 129>(ctx, gas, uint256_t{0x2ull});
            MONAD_AOT_TAIL return b_271<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_25b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x35, 0x18, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x35, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xc4ull});
            uint256_t const t2 = t1 ^ uint256_t{0x2ull};
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return b_271<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_266<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_266(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x52, 0x60, 0x61, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x52, 0x60, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1280u, 1312u, 126>(ctx, gas, uint256_t{0x0ull});
            aot::mstore_c<traits, 1312u, 1344u, 129>(ctx, gas, uint256_t{0x1ull});
            MONAD_AOT_TAIL return b_271<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_271(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_27d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_27d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x60, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x60, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1344u, 1376u, 132>(ctx, gas, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j8 = aot::nonzero(t2);
            top[0] = t1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_28c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_28c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x60, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x60, 0x35, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1376u, 1408u, 135>(ctx, gas, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j8 = aot::nonzero(t2);
            top[0] = t1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_29b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_29b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x11, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1408u, 1440u, 138>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1280u, 1312u, 126>(ctx, gas);
            uint256_t const t2 = aot::from_bool(uint256_t{0x2ull} < t1);
            bool const j8 = aot::nonzero(t2);
            top[0] = t1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2ab<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2ba<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x11, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x61, 0x51, 0x60, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1440u, 1472u, 142>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1312u, 1344u, 129>(ctx, gas);
            uint256_t const t2 = aot::from_bool(uint256_t{0x2ull} < t1);
            bool const j8 = aot::nonzero(t2);
            top[0] = t1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2ca<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ca(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2d9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x02, 0x61, 0x52, 0x6e, 0x61, 0x52, 0x60, 0x61, 0x51, 0x67, 0x02, 0x05, 0x6e, 0x01, 0x61, 0x51, 0x61, 0x61, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x02, 0x05, 0x02, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 1, 11));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1013)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x02, 0x61, 0x52, 0x6e, 0x61, 0x52, 0x60, 0x61, 0x51, 0x67, 0x02, 0x05, 0x6e, 0x01, 0x61, 0x51, 0x61, 0x61, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x02, 0x05, 0x02, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1472u, 1504u, 145>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, t1);
            aot::mstore_c<traits, 1504u, 1536u, 148>(ctx, gas, t3);
            aot::mstore_c<traits, 1536u, 1568u, 151>(ctx, gas, uint256_t{0x4902cd0097b425edull, 0x722112107720aull, 0x0ull, 0x0ull});
            uint256_t const t4 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t5 = aot::mul(uint256_t{0x1bc16d674ec80000ull}, t4);
            uint256_t const k17_1 = uint256_t{0x1bull};
            uint256_t r17;
            runtime::sdiv(&r17, &t5, &k17_1);
            uint256_t const t6 = uint256_t{0xdb086701c71c71c7ull, 0x1566336316561eull, 0x0ull, 0x0ull} + r17;
            uint256_t const t7 = aot::mload_c<traits, 1472u, 1504u, 145>(ctx, gas);
            uint256_t const t8 = aot::mload_c<traits, 1504u, 1536u, 148>(ctx, gas);
            uint256_t const t9 = aot::mload_c<traits, 1440u, 1472u, 142>(ctx, gas);
            uint256_t const t10 = aot::mload_c<traits, 1408u, 1440u, 138>(ctx, gas);
            uint256_t const t11 = aot::mload_c<traits, 1408u, 1440u, 138>(ctx, gas);
            uint256_t const t12 = aot::mul(t11, t10);
            uint256_t r33;
            runtime::sdiv(&r33, &t12, &t9);
            uint256_t const t13 = aot::mul(r33, t8);
            uint256_t const t14 = aot::mload_c<traits, 1344u, 1376u, 132>(ctx, gas);
            uint256_t const t15 = aot::mul(t13, t14);
            uint256_t const t16 = ~t14;
            uint256_t const t17 = aot::from_bool(!aot::nonzero(t16));
            uint256_t const t18 = aot::from_bool(!aot::nonzero(t17));
            uint256_t const t19 = aot::from_bool(t13 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t20 = aot::from_bool(!aot::nonzero(t19));
            uint256_t const t21 = t20 | t18;
            uint256_t const t22 = aot::from_bool(!aot::nonzero(t14));
            uint256_t r56;
            runtime::sdiv(&r56, &t15, &t14);
            uint256_t const t23 = aot::from_bool(r56 == t13);
            uint256_t const t24 = t23 | t22;
            uint256_t const t25 = t24 & t21;
            uint256_t const t26 = aot::from_bool(!aot::nonzero(t25));
            bool const j62 = aot::nonzero(t26);
            top[0] = t6;
            top[1] = t7;
            top[2] = uint256_t{0x2710ull};
            top[3] = uint256_t{0x2d9ull};
            top[4] = t13;
            top[5] = t14;
            top[6] = t15;
            top += 6;
            if (j62) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_35f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_35f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x05, 0x05, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x05, 0x05, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            uint256_t const &s4 = top[-4];
            uint256_t r5;
            runtime::sdiv(&r5, &r4, &s4);
            uint256_t const &s5 = top[-5];
            uint256_t r6;
            runtime::sdiv(&r6, &r5, &s5);
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s6 - r6;
            uint256_t const t2 = aot::from_bool(slt(s6, t1));
            uint256_t const t3 = aot::from_bool(slt(r6, uint256_t{0x0ull}));
            uint256_t const t4 = t3 ^ t2;
            bool const j18 = aot::nonzero(t4);
            top[-5] = r6;
            top[-4] = t1;
            top += -4;
            if (j18) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_374<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_374(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x67, 0x61, 0x51, 0x01, 0x61, 0x51, 0x02, 0x05, 0x6e, 0x01, 0x61, 0x60, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x01, 0x03, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 3, 10));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x67, 0x61, 0x51, 0x01, 0x61, 0x51, 0x02, 0x05, 0x6e, 0x01, 0x61, 0x60, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x01, 0x03, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1568u, 1600u, 154>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x3782dace9d900000ull};
            uint256_t const t3 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t4 = aot::mul(t3, t2);
            uint256_t const k14_1 = uint256_t{0x1bull};
            uint256_t r14;
            runtime::sdiv(&r14, &t4, &k14_1);
            uint256_t const t5 = uint256_t{0xdb086701c71c71c7ull, 0x1566336316561eull, 0x0ull, 0x0ull} + r14;
            uint256_t const t6 = aot::mload_c<traits, 1344u, 1376u, 132>(ctx, gas);
            uint256_t const t7 = aot::mload_c<traits, 1408u, 1440u, 138>(ctx, gas);
            uint256_t const t8 = aot::mload_c<traits, 1504u, 1536u, 148>(ctx, gas);
            uint256_t const t9 = aot::mload_c<traits, 1408u, 1440u, 138>(ctx, gas);
            uint256_t const t10 = aot::mload_c<traits, 1472u, 1504u, 145>(ctx, gas);
            uint256_t const t11 = aot::mload_c<traits, 1440u, 1472u, 142>(ctx, gas);
            uint256_t const t12 = t11 + t10;
            uint256_t const t13 = t12 - t9;
            uint256_t const t14 = aot::mul(t8, t13);
            uint256_t const t15 = ~t13;
            uint256_t const t16 = aot::from_bool(!aot::nonzero(t15));
            uint256_t const t17 = aot::from_bool(!aot::nonzero(t16));
            uint256_t const t18 = aot::from_bool(t8 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t19 = aot::from_bool(!aot::nonzero(t18));
            uint256_t const t20 = t19 | t17;
            uint256_t const t21 = aot::from_bool(!aot::nonzero(t13));
            uint256_t r52;
            runtime::sdiv(&r52, &t14, &t13);
            uint256_t const t22 = aot::from_bool(r52 == t8);
            uint256_t const t23 = t22 | t21;
            uint256_t const t24 = t23 & t20;
            uint256_t const t25 = aot::from_bool(!aot::nonzero(t24));
            bool const j58 = aot::nonzero(t25);
            top[-2] = t5;
            top[-1] = uint256_t{0x2710ull};
            top[0] = uint256_t{0x1bull};
            top[1] = t6;
            top[2] = t7;
            top[3] = t8;
            top[4] = t13;
            top[5] = t14;
            top += 5;
            if (j58) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_3e0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3e0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x02, 0x05, 0x05, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}, 8, 0));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x02, 0x05, 0x05, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::mul(r4, s4);
            uint256_t const &s5 = top[-5];
            uint256_t r6;
            runtime::sdiv(&r6, &t1, &s5);
            uint256_t const &s6 = top[-6];
            uint256_t r7;
            runtime::sdiv(&r7, &r6, &s6);
            uint256_t const &s7 = top[-7];
            uint256_t const t2 = s7 + r7;
            uint256_t const t3 = aot::from_bool(slt(t2, s7));
            uint256_t const t4 = aot::from_bool(slt(r7, uint256_t{0x0ull}));
            uint256_t const t5 = t4 ^ t3;
            bool const j19 = aot::nonzero(t5);
            top[-6] = r7;
            top[-5] = t2;
            top += -5;
            if (j19) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_3f6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3f6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x61, 0x51, 0x67, 0x01, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x61, 0x51, 0x67, 0x01, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1600u, 1632u, 158>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1376u, 1408u, 135>(ctx, gas);
            uint256_t const t2 = uint256_t{0xde0b6b3a7640000ull} + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x597d89b3754abea0ull, 0xb504f333f9de6484ull, 0x0ull, 0x0ull}));
            uint256_t const t4 = aot::from_bool(slt(uint256_t{0xa682764c8ab54160ull, 0x4afb0ccc06219b7bull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t2));
            uint256_t const t5 = t4 & t3;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j20 = aot::nonzero(t6);
            top[-2] = uint256_t{0x1bull};
            top[-1] = t2;
            top += -1;
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_44a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_44a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x60, 0x02, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x60, 0x02, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::exp_c<0x2u>(s0);
            uint256_t const &s1 = top[-1];
            uint256_t r5;
            runtime::sdiv(&r5, &t1, &s1);
            aot::mstore_c<traits, 1632u, 1664u, 161>(ctx, gas, r5);
            uint256_t const t2 = aot::mload_c<traits, 1536u, 1568u, 151>(ctx, gas);
            uint256_t const t3 = aot::mul(uint256_t{0x3ull}, t2);
            uint256_t const t4 = aot::mload_c<traits, 1600u, 1632u, 158>(ctx, gas);
            uint256_t const t5 = aot::mul(t3, t4);
            uint256_t const t6 = ~t4;
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            uint256_t const t9 = aot::from_bool(t3 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            uint256_t const t11 = t10 | t8;
            uint256_t const t12 = aot::from_bool(!aot::nonzero(t4));
            uint256_t r33;
            runtime::sdiv(&r33, &t5, &t4);
            uint256_t const t13 = aot::from_bool(r33 == t3);
            uint256_t const t14 = t13 | t12;
            uint256_t const t15 = t14 & t11;
            uint256_t const t16 = aot::from_bool(!aot::nonzero(t15));
            bool const j39 = aot::nonzero(t16);
            top[-1] = t3;
            top[0] = t4;
            top[1] = t5;
            top += 1;
            if (j39) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_47e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_47e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_48c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_48c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x5f, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x5f, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}) + 0;
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
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_4a2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4a2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
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
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_4b8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4b8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x7f, 0x81, 0x13, 0x15, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x7f, 0x81, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull}, s0));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top += -2;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x4e9); }
            MONAD_AOT_TAIL return b_4e4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4e4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_4f6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4f3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x5f, 0x03}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x5f, 0x03}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_4f6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_4f6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x61, 0x52, 0x5f, 0x61, 0x52, 0x73, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x61, 0x52, 0x5f, 0x61, 0x52, 0x73, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1664u, 1696u, 164>(ctx, gas, s0);
            aot::mstore_c<traits, 1696u, 1728u, 167>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t1 = aot::mload_c<traits, 1664u, 1696u, 164>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x7f41000000000001ull, 0xe4395d69670b12bull, 0xaf298d05ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j14 = aot::nonzero(t3);
            top += -2;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x64a); }
            MONAD_AOT_TAIL return b_521<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_521(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x72, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x72, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1664u, 1696u, 164>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x11d100000000001ull, 0x9673df52e37f2410ull, 0x47bf1ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x635); }
            MONAD_AOT_TAIL return b_53f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_53f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x70, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x70, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1664u, 1696u, 164>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0xb9f5610000000001ull, 0x6329f1c35ca4bfabull, 0x1dull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x621); }
            MONAD_AOT_TAIL return b_55b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_55b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x6e, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x6e, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1664u, 1696u, 164>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0xb34b9f1000000001ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x60f); }
            MONAD_AOT_TAIL return b_575<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_575(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x6d, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x6d, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1664u, 1696u, 164>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x85acef8100000001ull, 0x4ee2d6d415bull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x5ff); }
            MONAD_AOT_TAIL return b_58e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_58e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x6b, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x6b, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1664u, 1696u, 164>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x3e25026110000001ull, 0x204fce5eull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x5f0); }
            MONAD_AOT_TAIL return b_5a5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_5a5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x69, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x69, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1664u, 1696u, 164>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x1bcecceda1000001ull, 0xd3c2ull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_5e3<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_5ba<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_5ba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x68, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x68, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1664u, 1696u, 164>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x6bc75e2d63100001ull, 0x5ull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x5d8); }
            MONAD_AOT_TAIL return b_5ce<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_5ce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1696u, 1728u, 167>(ctx, gas, uint256_t{0x1ull});
            MONAD_AOT_TAIL return b_65d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_5e3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x62, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x62, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1696u, 1728u, 167>(ctx, gas, uint256_t{0xf4240ull});
            MONAD_AOT_TAIL return b_65d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_65d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x61, 0x52, 0x61, 0x51, 0x7f, 0x81, 0x13, 0x15, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x61, 0x52, 0x61, 0x51, 0x7f, 0x81, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1728u, 1760u, 170>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t1 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j11 = aot::nonzero(t3);
            top[1] = t1;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x694); }
            MONAD_AOT_TAIL return b_68f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_68f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_6a1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_69e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x5f, 0x03}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x5f, 0x03}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_6a1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_6a1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x61, 0x51, 0x7f, 0x81, 0x13, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x61, 0x51, 0x7f, 0x81, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1536u, 1568u, 151>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j10 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x6d5); }
            MONAD_AOT_TAIL return b_6d0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6d0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_6e2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6df(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x5f, 0x03}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x5f, 0x03}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_6e2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_6e2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x13, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x13, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(slt(s2, s0));
            bool const j5 = aot::nonzero(t1);
            top += -3;
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x79f); }
            MONAD_AOT_TAIL return b_6ea<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6ea(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x05, 0x7f, 0x81, 0x13, 0x15, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x05, 0x7f, 0x81, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1536u, 1568u, 151>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t r4;
            runtime::sdiv(&r4, &t2, &t1);
            uint256_t const t3 = aot::from_bool(slt(uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull}, r4));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j10 = aot::nonzero(t4);
            top[1] = r4;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x720); }
            MONAD_AOT_TAIL return b_71b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_71b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_72d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_72a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x5f, 0x03}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x5f, 0x03}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_72d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_72d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1728u, 1760u, 170>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1696u, 1728u, 167>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1536u, 1568u, 151>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 1728u, 1760u, 170>(ctx, gas);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j14 = aot::nonzero(t4);
            top[-1] = t1;
            top[0] = t2;
            top[1] = t3;
            top += 1;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_746<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_746(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x5f, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x5f, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}) + 0;
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
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_75c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_75c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x05, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x05, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x05, 0x05, 0x61, 0x52, 0x61, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x05, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x05, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x05, 0x05, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            aot::mstore_c<traits, 1536u, 1568u, 151>(ctx, gas, r4);
            uint256_t const t1 = aot::mload_c<traits, 1696u, 1728u, 167>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1728u, 1760u, 170>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t r13;
            runtime::sdiv(&r13, &t3, &t2);
            uint256_t r14;
            runtime::sdiv(&r14, &r13, &t1);
            aot::mstore_c<traits, 1568u, 1600u, 154>(ctx, gas, r14);
            uint256_t const t4 = aot::mload_c<traits, 1696u, 1728u, 167>(ctx, gas);
            uint256_t const t5 = aot::mload_c<traits, 1728u, 1760u, 170>(ctx, gas);
            uint256_t const t6 = aot::mload_c<traits, 1600u, 1632u, 158>(ctx, gas);
            uint256_t r23;
            runtime::sdiv(&r23, &t6, &t5);
            uint256_t r24;
            runtime::sdiv(&r24, &r23, &t4);
            aot::mstore_c<traits, 1600u, 1632u, 158>(ctx, gas, r24);
            uint256_t const t7 = aot::mload_c<traits, 1696u, 1728u, 167>(ctx, gas);
            uint256_t const t8 = aot::mload_c<traits, 1728u, 1760u, 170>(ctx, gas);
            uint256_t const t9 = aot::mload_c<traits, 1632u, 1664u, 161>(ctx, gas);
            uint256_t r33;
            runtime::sdiv(&r33, &t9, &t8);
            uint256_t r34;
            runtime::sdiv(&r34, &r33, &t7);
            aot::mstore_c<traits, 1632u, 1664u, 161>(ctx, gas, r34);
            top += -4;
            MONAD_AOT_TAIL return b_895<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_7d1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x7e3);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_7e0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x5f, 0x03}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x5f, 0x03}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x7e3);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_826(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            aot::mstore_c<traits, 1568u, 1600u, 154>(ctx, gas, r4);
            uint256_t const t1 = aot::mload_c<traits, 1696u, 1728u, 167>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1600u, 1632u, 158>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 1728u, 1760u, 170>(ctx, gas);
            uint256_t const t4 = aot::mul(t2, t3);
            uint256_t const t5 = ~t3;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = aot::from_bool(t2 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            uint256_t const t10 = t9 | t7;
            uint256_t const t11 = aot::from_bool(!aot::nonzero(t3));
            uint256_t r32;
            runtime::sdiv(&r32, &t4, &t3);
            uint256_t const t12 = aot::from_bool(r32 == t2);
            uint256_t const t13 = t12 | t11;
            uint256_t const t14 = t13 & t10;
            uint256_t const t15 = aot::from_bool(!aot::nonzero(t14));
            bool const j38 = aot::nonzero(t15);
            top[-3] = t1;
            top[-2] = t2;
            top[-1] = t3;
            top[0] = t4;
            if (j38) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_859<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_859(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            aot::mstore_c<traits, 1600u, 1632u, 158>(ctx, gas, r4);
            uint256_t const t1 = aot::mload_c<traits, 1696u, 1728u, 167>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1632u, 1664u, 161>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 1728u, 1760u, 170>(ctx, gas);
            uint256_t const t4 = aot::mul(t2, t3);
            uint256_t const t5 = ~t3;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = aot::from_bool(t2 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            uint256_t const t10 = t9 | t7;
            uint256_t const t11 = aot::from_bool(!aot::nonzero(t3));
            uint256_t r32;
            runtime::sdiv(&r32, &t4, &t3);
            uint256_t const t12 = aot::from_bool(r32 == t2);
            uint256_t const t13 = t12 | t11;
            uint256_t const t14 = t13 & t10;
            uint256_t const t15 = aot::from_bool(!aot::nonzero(t14));
            bool const j38 = aot::nonzero(t15);
            top[-3] = t1;
            top[-2] = t2;
            top[-1] = t3;
            top[0] = t4;
            if (j38) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_88c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_88c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            aot::mstore_c<traits, 1632u, 1664u, 161>(ctx, gas, r4);
            top += -4;
            MONAD_AOT_TAIL return b_895<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_895(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x60, 0x02, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 0, 8));
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x60, 0x02, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1536u, 1568u, 151>(ctx, gas);
            uint256_t const t2 = aot::mul(uint256_t{0x3ull}, t1);
            uint256_t const t3 = aot::mload_c<traits, 1600u, 1632u, 158>(ctx, gas);
            uint256_t const t4 = aot::mul(t2, t3);
            uint256_t const t5 = ~t3;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = aot::from_bool(t2 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            uint256_t const t10 = t9 | t7;
            uint256_t const t11 = aot::from_bool(!aot::nonzero(t3));
            uint256_t r26;
            runtime::sdiv(&r26, &t4, &t3);
            uint256_t const t12 = aot::from_bool(r26 == t2);
            uint256_t const t13 = t12 | t11;
            uint256_t const t14 = t13 & t10;
            uint256_t const t15 = aot::from_bool(!aot::nonzero(t14));
            bool const j32 = aot::nonzero(t15);
            top[1] = t2;
            top[2] = t3;
            top[3] = t4;
            top += 3;
            if (j32) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_8bf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_8bf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x05, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x05, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1760u, 1792u, 174>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1760u, 1792u, 174>(ctx, gas);
            uint256_t r10;
            runtime::sdiv(&r10, &t2, &t1);
            uint256_t const t3 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t4 = r10 - t3;
            uint256_t const t5 = aot::from_bool(slt(r10, t4));
            uint256_t const t6 = aot::from_bool(slt(t3, uint256_t{0x0ull}));
            uint256_t const t7 = t6 ^ t5;
            bool const j24 = aot::nonzero(t7);
            top[-2] = r10;
            top[-1] = t3;
            top[0] = t4;
            if (j24) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_8e2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_8e2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x05, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1792u, 1824u, 177>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1760u, 1792u, 174>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0x3ull});
            uint256_t const k16_1 = uint256_t{0x3ull};
            uint256_t r16;
            runtime::sdiv(&r16, &t3, &k16_1);
            uint256_t const t4 = r16 ^ t2;
            bool const j19 = aot::nonzero(t4);
            top[-2] = t1;
            top[-1] = t2;
            top[0] = t3;
            if (j19) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_900<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_900(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x05, 0x61, 0x51, 0x60, 0x1b, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x05, 0x61, 0x51, 0x60, 0x1b, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t r2;
            runtime::sdiv(&r2, &s0, &s2);
            uint256_t const t1 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t2 = aot::shl_c<1>(t1);
            uint256_t const t3 = r2 - t2;
            uint256_t const t4 = aot::from_bool(slt(r2, t3));
            uint256_t const t5 = aot::from_bool(slt(t2, uint256_t{0x0ull}));
            uint256_t const t6 = t5 ^ t4;
            bool const j18 = aot::nonzero(t6);
            top[-2] = r2;
            top[-1] = t2;
            top[0] = t3;
            if (j18) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_918<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_918(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 1536u, 1568u, 151>(ctx, gas);
            uint256_t const t4 = aot::from_bool(slt(t3, uint256_t{0x597d89b3754abea0ull, 0xb504f333f9de6484ull, 0x0ull, 0x0ull}));
            uint256_t const t5 = aot::from_bool(slt(uint256_t{0xa682764c8ab54160ull, 0x4afb0ccc06219b7bull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t3));
            uint256_t const t6 = t5 & t4;
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            bool const j19 = aot::nonzero(t7);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = t2;
            top[1] = t3;
            top += 1;
            if (j19) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_964<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_964(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_978<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_978(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x05, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x05, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t r2;
            runtime::sdiv(&r2, &s0, &s2);
            uint256_t const t1 = aot::mload_c<traits, 1632u, 1664u, 161>(ctx, gas);
            uint256_t const t2 = aot::mul(r2, t1);
            uint256_t const t3 = ~t1;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(r2 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t1));
            uint256_t r24;
            runtime::sdiv(&r24, &t2, &t1);
            uint256_t const t10 = aot::from_bool(r24 == r2);
            uint256_t const t11 = t10 | t9;
            uint256_t const t12 = t11 & t8;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t12));
            bool const j30 = aot::nonzero(t13);
            top[-2] = r2;
            top[-1] = t1;
            top[0] = t2;
            if (j30) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_99d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_99d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}, 5, 1));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s4 - r4;
            uint256_t const t2 = aot::from_bool(slt(s4, t1));
            uint256_t const t3 = aot::from_bool(slt(r4, uint256_t{0x0ull}));
            uint256_t const t4 = t3 ^ t2;
            bool const j16 = aot::nonzero(t4);
            top[-3] = r4;
            top[-2] = t1;
            top += -2;
            if (j16) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_9b0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9b0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1824u, 1856u, 180>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1824u, 1856u, 180>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x597d89b3754abea0ull, 0xb504f333f9de6484ull, 0x0ull, 0x0ull}));
            uint256_t const t3 = aot::from_bool(slt(uint256_t{0xa682764c8ab54160ull, 0x4afb0ccc06219b7bull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t1));
            uint256_t const t4 = t3 & t2;
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            bool const j17 = aot::nonzero(t5);
            top[-2] = t1;
            top += -2;
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_9f8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9f8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x61, 0x51, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x0a, 0x90, 0x50, 0x61, 0x51, 0x61, 0x51, 0x6f, 0x81, 0x12, 0x7f, 0x82, 0x13, 0x16, 0x15, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::exp_c<0x2u>(s0);
            uint256_t const t2 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 1792u, 1824u, 177>(ctx, gas);
            uint256_t const t4 = aot::from_bool(slt(t3, uint256_t{0x597d89b3754abea0ull, 0xb504f333f9de6484ull, 0x0ull, 0x0ull}));
            uint256_t const t5 = aot::from_bool(slt(uint256_t{0xa682764c8ab54160ull, 0x4afb0ccc06219b7bull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t3));
            uint256_t const t6 = t5 & t4;
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            bool const j18 = aot::nonzero(t7);
            top[0] = t1;
            top[1] = t2;
            top[2] = t3;
            top += 2;
            if (j18) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_a42<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a42(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_a56<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a56(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x05, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x05, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t r2;
            runtime::sdiv(&r2, &s0, &s2);
            uint256_t const t1 = aot::mload_c<traits, 1792u, 1824u, 177>(ctx, gas);
            uint256_t const t2 = aot::mul(r2, t1);
            uint256_t const t3 = ~t1;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(r2 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t1));
            uint256_t r24;
            runtime::sdiv(&r24, &t2, &t1);
            uint256_t const t10 = aot::from_bool(r24 == r2);
            uint256_t const t11 = t10 | t9;
            uint256_t const t12 = t11 & t8;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t12));
            bool const j30 = aot::nonzero(t13);
            top[-2] = r2;
            top[-1] = t1;
            top[0] = t2;
            if (j30) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_a7b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a7b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s3 + s0;
            uint256_t const t2 = aot::from_bool(slt(t1, s3));
            uint256_t const t3 = aot::from_bool(slt(s0, uint256_t{0x0ull}));
            uint256_t const t4 = t3 ^ t2;
            bool const j15 = aot::nonzero(t4);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_a8d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a8d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x5f, 0x61, 0x52, 0x60, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x5f, 0x61, 0x52, 0x60, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1856u, 1888u, 183>(ctx, gas, s0);
            aot::mstore_c<traits, 1888u, 1920u, 187>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t1 = aot::mload_c<traits, 1856u, 1888u, 183>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x1ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j15 = aot::nonzero(t3);
            top += -3;
            if (j15) { MONAD_AOT_TAIL return b_adf<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_aa6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_aa6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x61, 0x37, 0x60, 0x60, 0x61, 0x37, 0x60, 0x60, 0x61, 0x37, 0x61, 0x61, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x61, 0x37, 0x60, 0x60, 0x61, 0x37, 0x60, 0x60, 0x61, 0x37, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const k3_0 = uint256_t{0x120ull};
            uint256_t const k3_1 = uint256_t{0x4ull};
            uint256_t const k3_2 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k3_0, &k3_1, &k3_2);
            gas = ctx->gas_remaining;
            uint256_t const k7_0 = uint256_t{0x160ull};
            uint256_t const k7_1 = uint256_t{0x44ull};
            uint256_t const k7_2 = uint256_t{0x60ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k7_0, &k7_1, &k7_2);
            gas = ctx->gas_remaining;
            uint256_t const k11_0 = uint256_t{0x1c0ull};
            uint256_t const k11_1 = uint256_t{0xa4ull};
            uint256_t const k11_2 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k11_0, &k11_1, &k11_2);
            gas = ctx->gas_remaining;
            top[1] = uint256_t{0xac8ull};
            top[2] = uint256_t{0x780ull};
            top += 2;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b13);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_adf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x5f, 0x81, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x5f, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1856u, 1888u, 183>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_aeb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_aeb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j6) { MONAD_AOT_TAIL return b_b13<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_b07<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b07(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_b13<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_b13(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x69, 0x82, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x69, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < uint256_t{0x0ull, 0x100ull, 0x0ull, 0x0ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_b31<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_b25<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b25(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_b31<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_b31(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x65, 0x82, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x65, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < uint256_t{0x10000000000ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_b4b<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_b3f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b3f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_b4b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_b4b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x82, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < uint256_t{0x1000000ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_b63<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_b57<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b57(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_b63<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_b63(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j97) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_bd3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_bd3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x5f, 0x61, 0x52, 0x5f, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x5f, 0x61, 0x52, 0x5f, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1888u, 1920u, 187>(ctx, gas, s0);
            aot::mstore_c<traits, 1920u, 1952u, 190>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t1 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j11 = aot::nonzero(t3);
            top += -1;
            if (j11) { MONAD_AOT_TAIL return b_c66<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_be7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_be7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x7f, 0x81, 0x14, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x7f, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t2 = aot::from_bool(t1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            bool const j6 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_c12<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c12(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x03, 0x5f, 0x81, 0x12, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x03, 0x5f, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            bool const j6 = aot::nonzero(t2);
            top[0] = t1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_c1b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c1b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, s0);
            top[0] = uint256_t{0xc28ull};
            top[1] = uint256_t{0x7a0ull};
            top += 1;
            MONAD_AOT_TAIL return b_24aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c35(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x81, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(s0 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_c5c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c5c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x03, 0x61, 0x52, 0x61, 0x56}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x03, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            aot::mstore_c<traits, 1920u, 1952u, 190>(ctx, gas, t1);
            top += -1;
            MONAD_AOT_TAIL return b_c90<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c66(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x5f, 0x81, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x5f, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_c72<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c72(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, s0);
            top[0] = uint256_t{0xc7full};
            top[1] = uint256_t{0x7a0ull};
            top += 1;
            MONAD_AOT_TAIL return b_24aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c7f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1952u, 1984u, 193>(ctx, gas);
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_c8c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c8c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1920u, 1952u, 190>(ctx, gas, s0);
            top += -1;
            MONAD_AOT_TAIL return b_c90<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c90(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x61, 0x52, 0x60, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x61, 0x52, 0x60, 0x61, 0x51, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1952u, 1984u, 193>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t1 = aot::mload_c<traits, 1824u, 1856u, 180>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x1ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j10 = aot::nonzero(t3);
            if (j10) { MONAD_AOT_TAIL return b_d3a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_ca2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ca2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}, 0, 6));
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1824u, 1856u, 180>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1888u, 1920u, 187>(ctx, gas);
            uint256_t const t3 = t1 - t2;
            uint256_t const t4 = aot::from_bool(slt(t1, t3));
            uint256_t const t5 = aot::from_bool(slt(t2, uint256_t{0x0ull}));
            uint256_t const t6 = t5 ^ t4;
            bool const j15 = aot::nonzero(t6);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_cb8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_cb8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x7f, 0x81, 0x14, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x7f, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(s0 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            bool const j8 = aot::nonzero(t1);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top += -2;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_ce3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ce3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x03, 0x5f, 0x81, 0x12, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x03, 0x5f, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            bool const j6 = aot::nonzero(t2);
            top[0] = t1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_cec<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_cec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1c, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1c, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shr_c<1>(s0);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t1);
            top[0] = uint256_t{0xcfcull};
            top[1] = uint256_t{0x7c0ull};
            top += 1;
            MONAD_AOT_TAIL return b_24aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d09(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x81, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(s0 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_d30<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d30(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x03, 0x61, 0x52, 0x61, 0x56}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x03, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            aot::mstore_c<traits, 1952u, 1984u, 193>(ctx, gas, t1);
            top += -1;
            MONAD_AOT_TAIL return b_d7d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d3a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}, 0, 6));
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1824u, 1856u, 180>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1888u, 1920u, 187>(ctx, gas);
            uint256_t const t3 = t1 + t2;
            uint256_t const t4 = aot::from_bool(slt(t3, t1));
            uint256_t const t5 = aot::from_bool(slt(t2, uint256_t{0x0ull}));
            uint256_t const t6 = t5 ^ t4;
            bool const j16 = aot::nonzero(t6);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j16) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_d51<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d51(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x5f, 0x81, 0x12, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x5f, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(slt(s0, uint256_t{0x0ull}));
            bool const j8 = aot::nonzero(t1);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top += -2;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_d5c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d5c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1c, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1c, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shr_c<1>(s0);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t1);
            top[0] = uint256_t{0xd6cull};
            top[1] = uint256_t{0x7c0ull};
            top += 1;
            MONAD_AOT_TAIL return b_24aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d6c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x80, 0x60, 0x1c, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1984u, 2016u, 196>(ctx, gas);
            uint256_t const t2 = aot::shr_c<255>(t1);
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_d79<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d79(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1952u, 1984u, 193>(ctx, gas, s0);
            top += -1;
            MONAD_AOT_TAIL return b_d7d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d7d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x67, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 0, 10));
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x67, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1920u, 1952u, 190>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1920u, 1952u, 190>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = ~t2;
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const t7 = aot::from_bool(t1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            uint256_t const t9 = t8 | t6;
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t2));
            uint256_t r26;
            runtime::sdiv(&r26, &t3, &t2);
            uint256_t const t11 = aot::from_bool(r26 == t1);
            uint256_t const t12 = t11 | t10;
            uint256_t const t13 = t12 & t9;
            uint256_t const t14 = aot::from_bool(!aot::nonzero(t13));
            bool const j32 = aot::nonzero(t14);
            top[1] = uint256_t{0xde0b6b3a7640000ull};
            top[2] = uint256_t{0xde0b6b3a7640000ull};
            top[3] = t1;
            top[4] = t2;
            top[5] = t3;
            top += 5;
            if (j32) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_db6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_db6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            uint256_t const t1 = aot::mload_c<traits, 1952u, 1984u, 193>(ctx, gas);
            uint256_t const t2 = aot::mul(r4, t1);
            uint256_t const t3 = ~t1;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(r4 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t1));
            uint256_t r26;
            runtime::sdiv(&r26, &t2, &t1);
            uint256_t const t10 = aot::from_bool(r26 == r4);
            uint256_t const t11 = t10 | t9;
            uint256_t const t12 = t11 & t8;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t12));
            bool const j32 = aot::nonzero(t13);
            top[-3] = r4;
            top[-2] = t1;
            top[-1] = t2;
            top += -1;
            if (j32) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_ddd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ddd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 4, 6));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52, 0x60, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            aot::mstore_c<traits, 1984u, 2016u, 196>(ctx, gas, r4);
            uint256_t const t1 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1568u, 1600u, 154>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 1792u, 1824u, 177>(ctx, gas);
            uint256_t const t4 = aot::mul(t2, t3);
            uint256_t const t5 = ~t3;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = aot::from_bool(t2 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            uint256_t const t10 = t9 | t7;
            uint256_t const t11 = aot::from_bool(!aot::nonzero(t3));
            uint256_t r33;
            runtime::sdiv(&r33, &t4, &t3);
            uint256_t const t12 = aot::from_bool(r33 == t2);
            uint256_t const t13 = t12 | t11;
            uint256_t const t14 = t13 & t10;
            uint256_t const t15 = aot::from_bool(!aot::nonzero(t14));
            bool const j39 = aot::nonzero(t15);
            top[-3] = uint256_t{0x3ull};
            top[-2] = t1;
            top[-1] = t2;
            top[0] = t3;
            top[1] = t4;
            top += 1;
            if (j39) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_e12<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e12(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1984u, 2016u, 196>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_e20<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e20(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x5f, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x05, 0x60, 0x60, 0x1b, 0x83, 0x14, 0x15, 0x5f, 0x19, 0x83, 0x14, 0x15, 0x17, 0x15, 0x61, 0x57}) + 0;
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
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_e36<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e36(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x82, 0x01, 0x82, 0x81, 0x12, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s3 + s0;
            uint256_t const t2 = aot::from_bool(slt(t1, s3));
            uint256_t const t3 = aot::from_bool(slt(s0, uint256_t{0x0ull}));
            uint256_t const t4 = t3 ^ t2;
            bool const j15 = aot::nonzero(t4);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_e48<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e48(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x13, 0x5f, 0x83, 0x12, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1984u, 2016u, 196>(ctx, gas);
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
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_e5e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e5e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x60, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 4, 8));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x60, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            aot::mstore_c<traits, 2016u, 2048u, 200>(ctx, gas, r4);
            uint256_t const t1 = aot::mload_c<traits, 1536u, 1568u, 151>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1440u, 1472u, 142>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 1472u, 1504u, 145>(ctx, gas);
            uint256_t const t4 = aot::mload_c<traits, 1408u, 1440u, 138>(ctx, gas);
            uint256_t const t5 = aot::mload_c<traits, 1408u, 1440u, 138>(ctx, gas);
            uint256_t const t6 = aot::mul(t4, t5);
            uint256_t const t7 = ~t5;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            uint256_t const t10 = aot::from_bool(t4 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t11 = aot::from_bool(!aot::nonzero(t10));
            uint256_t const t12 = t11 | t9;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t5));
            uint256_t r37;
            runtime::sdiv(&r37, &t6, &t5);
            uint256_t const t14 = aot::from_bool(r37 == t4);
            uint256_t const t15 = t14 | t13;
            uint256_t const t16 = t15 & t12;
            uint256_t const t17 = aot::from_bool(!aot::nonzero(t16));
            bool const j43 = aot::nonzero(t17);
            top[-3] = t1;
            top[-2] = t2;
            top[-1] = t3;
            top[0] = uint256_t{0x1bull};
            top[1] = t4;
            top[2] = t5;
            top[3] = t6;
            top += 3;
            if (j43) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_e9b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e9b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x05, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x05, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            uint256_t const &s4 = top[-4];
            uint256_t r5;
            runtime::sdiv(&r5, &r4, &s4);
            uint256_t const t1 = aot::mload_c<traits, 1408u, 1440u, 138>(ctx, gas);
            uint256_t const t2 = aot::mul(r5, t1);
            uint256_t const t3 = ~t1;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(r5 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t1));
            uint256_t r27;
            runtime::sdiv(&r27, &t2, &t1);
            uint256_t const t10 = aot::from_bool(r27 == r5);
            uint256_t const t11 = t10 | t9;
            uint256_t const t12 = t11 & t8;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t12));
            bool const j33 = aot::nonzero(t13);
            top[-4] = r5;
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j33) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_ec3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ec3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x19, 0x15, 0x15, 0x60, 0x60, 0x1b, 0x84, 0x14, 0x15, 0x17, 0x82, 0x15, 0x84, 0x84, 0x84, 0x05, 0x14, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            uint256_t const t1 = aot::mload_c<traits, 2016u, 2048u, 200>(ctx, gas);
            uint256_t const t2 = aot::mul(r4, t1);
            uint256_t const t3 = ~t1;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(r4 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t1));
            uint256_t r26;
            runtime::sdiv(&r26, &t2, &t1);
            uint256_t const t10 = aot::from_bool(r26 == r4);
            uint256_t const t11 = t10 | t9;
            uint256_t const t12 = t11 & t8;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t12));
            bool const j32 = aot::nonzero(t13);
            top[-3] = r4;
            top[-2] = t1;
            top[-1] = t2;
            top += -1;
            if (j32) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_eea<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_eea(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x5f, 0x81, 0x12, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x05, 0x61, 0x52, 0x61, 0x51, 0x5f, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::sdiv(&r4, &s0, &s3);
            aot::mstore_c<traits, 2048u, 2080u, 203>(ctx, gas, r4);
            uint256_t const t1 = aot::mload_c<traits, 2048u, 2080u, 203>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            bool const j13 = aot::nonzero(t2);
            top[-3] = t1;
            top += -3;
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_efe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_efe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x05, 0x18, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x05, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 2080u, 2112u, 206>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1536u, 1568u, 151>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 2016u, 2048u, 200>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const k12_1 = uint256_t{0xde0b6b3a7640000ull};
            uint256_t r12;
            runtime::sdiv(&r12, &t3, &k12_1);
            uint256_t const t4 = r12 ^ t2;
            bool const j15 = aot::nonzero(t4);
            top[0] = t1;
            top[1] = t2;
            top[2] = t3;
            top += 2;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_f26<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f26(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x05, 0x5f, 0x81, 0x12, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x05, 0x5f, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t r2;
            runtime::sdiv(&r2, &s0, &s2);
            uint256_t const t1 = aot::from_bool(slt(r2, uint256_t{0x0ull}));
            bool const j7 = aot::nonzero(t1);
            top[-2] = r2;
            top += -2;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_f30<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f30(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x60, 0x35, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x60, 0x35, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 2112u, 2144u, 209>(ctx, gas, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const t2 = aot::mload_c<traits, 2080u, 2112u, 206>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = aot::udiv(t3, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t5 = t4 ^ t2;
            bool const j15 = aot::nonzero(t5);
            top[0] = t1;
            top[1] = t2;
            top[2] = t3;
            top += 2;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_f57<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f57(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x04, 0x61, 0x52, 0x66, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x04, 0x61, 0x52, 0x66, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::udiv(s0, s2);
            aot::mstore_c<traits, 1248u, 1280u, 123>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 1248u, 1280u, 123>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t2 < uint256_t{0x2386f26fc0ffffull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j11 = aot::nonzero(t4);
            top += -3;
            if (j11) { MONAD_AOT_TAIL return b_f75<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_f70<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f70(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_f86<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f75(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x68, 0x61, 0x51, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x68, 0x61, 0x51, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1248u, 1280u, 123>(ctx, gas);
            uint256_t const t2 = aot::from_bool(uint256_t{0x6bc75e2d63100000ull, 0x5ull, 0x0ull, 0x0ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_f86<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f86(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j2 = aot::nonzero(s0);
            top += -1;
            if (j2) { MONAD_AOT_TAIL return b_fef<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_f8b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f8b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 2144u, 2176u, 213>(ctx, gas, uint256_t{0x12ull});
            aot::mstore_c<traits, 2176u, 2208u, 216>(ctx, gas, uint256_t{0x0ull, 0x2079000000000000ull, 0x616c756520666f72ull, 0x556e736166652076ull});
            uint256_t const t1 = aot::mload_c<traits, 2144u, 2176u, 213>(ctx, gas);
            uint256_t const t2 = uint256_t{0x880ull} + t1;
            uint256_t const t3 = uint256_t{0x0ull} - t1;
            uint256_t const t4 = t3 & uint256_t{0x1full};
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t2, &t5, &t4);
            gas = ctx->gas_remaining;
            aot::mstore_c<traits, 2080u, 2112u, 206>(ctx, gas, uint256_t{0x8c379a0ull});
            aot::mstore_c<traits, 2112u, 2144u, 209>(ctx, gas, uint256_t{0x20ull});
            uint256_t const t6 = aot::mload_c<traits, 2144u, 2176u, 213>(ctx, gas);
            uint256_t const t7 = t6 + uint256_t{0x1full};
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t9 = uint256_t{0x44ull} + t8;
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x83cull}, t9);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fef(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x61}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x61}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x40ull};
            top[2] = uint256_t{0x820ull};
            top += 2;
            MONAD_AOT_TAIL return b_ff5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ff5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
        [[gnu::noinline]] void b_ff7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0xc7fab708ull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1014<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1003<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1003(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xa4ull});
            bool const j4 = aot::nonzero(t2);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_100b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_100b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 512u, 544u, 51>(ctx, gas, uint256_t{0x0ull});
            MONAD_AOT_TAIL return b_102f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1014(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0x7b12e009ull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_167c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1020<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1020(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xc4ull});
            bool const j4 = aot::nonzero(t2);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1028<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1028(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x61, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            aot::mstore_c<traits, 512u, 544u, 51>(ctx, gas, t1);
            MONAD_AOT_TAIL return b_102f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_102f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x60, 0x37, 0x61, 0x61, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x60, 0x37, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const k4_0 = uint256_t{0x40ull};
            uint256_t const k4_1 = uint256_t{0x44ull};
            uint256_t const k4_2 = uint256_t{0x60ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k4_0, &k4_1, &k4_2);
            gas = ctx->gas_remaining;
            top[1] = uint256_t{0x1041ull};
            top[2] = uint256_t{0x280ull};
            top += 2;
            MONAD_AOT_TAIL return b_1a86<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1041(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x80, 0x51, 0x61, 0x52, 0x60, 0x81, 0x01, 0x51, 0x61, 0x52, 0x60, 0x81, 0x01, 0x51, 0x61, 0x52, 0x50, 0x79, 0x61, 0x51, 0x11, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x80, 0x51, 0x61, 0x52, 0x60, 0x81, 0x01, 0x51, 0x61, 0x52, 0x60, 0x81, 0x01, 0x51, 0x61, 0x52, 0x50, 0x79, 0x61, 0x51, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 640u, 672u, 63>(ctx, gas);
            aot::mstore_c<traits, 544u, 576u, 54>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            aot::mstore_c<traits, 576u, 608u, 57>(ctx, gas, t2);
            uint256_t const t3 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            aot::mstore_c<traits, 608u, 640u, 60>(ctx, gas, t3);
            uint256_t const t4 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t5 = aot::from_bool(uint256_t{0x98d506d374fd487aull, 0x1d495c8ba43b5b4bull, 0xfe5212d2319f867ull, 0x1f2ull} < t4);
            bool const j24 = aot::nonzero(t5);
            if (j24) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1082<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1082(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j4 = aot::nonzero(t2);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_108b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_108b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x01, 0x01, 0x61, 0x52, 0x5f, 0x61, 0x52, 0x61, 0x51, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x01, 0x01, 0x61, 0x52, 0x5f, 0x61, 0x52, 0x61, 0x51, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 608u, 640u, 60>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 576u, 608u, 57>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t4 = t3 + t2;
            uint256_t const t5 = t4 + t1;
            aot::mstore_c<traits, 640u, 672u, 63>(ctx, gas, t5);
            aot::mstore_c<traits, 672u, 704u, 66>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t6 = aot::mload_c<traits, 512u, 544u, 51>(ctx, gas);
            bool const j16 = aot::nonzero(t6);
            if (j16) { MONAD_AOT_TAIL return b_10dc<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_10aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10aa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x61, 0x61, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            aot::mstore_c<traits, 352u, 384u, 36>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 576u, 608u, 57>(ctx, gas);
            aot::mstore_c<traits, 384u, 416u, 39>(ctx, gas, t2);
            uint256_t const t3 = aot::mload_c<traits, 608u, 640u, 60>(ctx, gas);
            aot::mstore_c<traits, 416u, 448u, 42>(ctx, gas, t3);
            top[1] = uint256_t{0x10ccull};
            top[2] = uint256_t{0x2c0ull};
            top += 2;
            MONAD_AOT_TAIL return b_26b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_10cc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x60, 0x02, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x60, 0x02, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t2 = aot::mul(uint256_t{0x3ull}, t1);
            aot::mstore_c<traits, 672u, 704u, 66>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_1286<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_10dc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x6e, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x6e, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 640u, 672u, 63>(ctx, gas);
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xb34b9f1000000001ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11fd); }
            MONAD_AOT_TAIL return b_10f7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10f7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x69, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x69, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 640u, 672u, 63>(ctx, gas);
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x1bcecceda1000001ull, 0xd3c2ull, 0x0ull, 0x0ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_1179<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_110c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_110c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x67, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 0, 9));
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x67, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 512u, 544u, 51>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 576u, 608u, 57>(ctx, gas);
            uint256_t const t4 = aot::mul(t2, t3);
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t6 = aot::udiv(t4, t3);
            uint256_t const t7 = aot::from_bool(t6 == t2);
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            bool const j20 = aot::nonzero(t9);
            top[1] = t1;
            top[2] = uint256_t{0xde0b6b3a7640000ull};
            top[3] = t2;
            top[4] = t3;
            top[5] = t4;
            top += 5;
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1131<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1131(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mload_c<traits, 608u, 640u, 60>(ctx, gas);
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
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_114a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_114a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mul(t1, uint256_t{0x1bull});
            uint256_t const t3 = aot::udiv(t2, uint256_t{0x1bull});
            uint256_t const t4 = t3 ^ t1;
            bool const j14 = aot::nonzero(t4);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_115d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_115d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, s0);
            top[-1] = uint256_t{0x116cull};
            top[0] = uint256_t{0x2c0ull};
            MONAD_AOT_TAIL return b_24aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_116c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            aot::mstore_c<traits, 672u, 704u, 66>(ctx, gas, t1);
            MONAD_AOT_TAIL return b_1286<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1179(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x69, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 0, 9));
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x69, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 512u, 544u, 51>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 576u, 608u, 57>(ctx, gas);
            uint256_t const t4 = aot::mul(t2, t3);
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t6 = aot::udiv(t4, t3);
            uint256_t const t7 = aot::from_bool(t6 == t2);
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            bool const j21 = aot::nonzero(t9);
            top[1] = t1;
            top[2] = uint256_t{0x1bcecceda1000000ull, 0xd3c2ull, 0x0ull, 0x0ull};
            top[3] = t2;
            top[4] = t3;
            top[5] = t4;
            top += 5;
            if (j21) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_11a1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11a1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mload_c<traits, 608u, 640u, 60>(ctx, gas);
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
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_11ba<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11ba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mul(t1, uint256_t{0x1bull});
            uint256_t const t3 = aot::udiv(t2, uint256_t{0x1bull});
            uint256_t const t4 = t3 ^ t1;
            bool const j14 = aot::nonzero(t4);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_11cd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11cd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x62, 0x81, 0x02, 0x81, 0x62, 0x82, 0x04, 0x18, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x62, 0x81, 0x02, 0x81, 0x62, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(s0, uint256_t{0xf4240ull});
            uint256_t const t2 = aot::udiv(t1, uint256_t{0xf4240ull});
            uint256_t const t3 = t2 ^ s0;
            bool const j11 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_11e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11e1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, s0);
            top[-1] = uint256_t{0x11f0ull};
            top[0] = uint256_t{0x2c0ull};
            MONAD_AOT_TAIL return b_24aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_11f0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            aot::mstore_c<traits, 672u, 704u, 66>(ctx, gas, t1);
            MONAD_AOT_TAIL return b_1286<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_122a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mload_c<traits, 608u, 640u, 60>(ctx, gas);
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
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1243<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1243(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mul(t1, uint256_t{0x1bull});
            uint256_t const t3 = aot::udiv(t2, uint256_t{0x1bull});
            uint256_t const t4 = t3 ^ t1;
            bool const j14 = aot::nonzero(t4);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1256<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1256(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x64, 0x81, 0x02, 0x81, 0x64, 0x82, 0x04, 0x18, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x64, 0x81, 0x02, 0x81, 0x64, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(s0, uint256_t{0xe8d4a51000ull});
            uint256_t const t2 = aot::udiv(t1, uint256_t{0xe8d4a51000ull});
            uint256_t const t3 = t2 ^ s0;
            bool const j11 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_126e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_126e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, s0);
            top[-1] = uint256_t{0x127dull};
            top[0] = uint256_t{0x2c0ull};
            MONAD_AOT_TAIL return b_24aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1286(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x36, 0x61, 0x37, 0x5f, 0x60, 0x90}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x36, 0x61, 0x37, 0x5f, 0x60, 0x90}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const k4_0 = uint256_t{0x2c0ull};
            uint256_t const k4_2 = uint256_t{0x140ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k4_0, &t1, &k4_2);
            gas = ctx->gas_remaining;
            top[1] = uint256_t{0xffull};
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_1293<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1293(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x60, 0x61, 0x51, 0x61, 0x51, 0x60, 0x61, 0x51, 0x61, 0x51, 0x60, 0x61, 0x51, 0x67, 0x02, 0x02, 0x04, 0x02, 0x02, 0x04, 0x02, 0x02, 0x04, 0x61, 0x52, 0x67, 0x60, 0x35, 0x01, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}, 1, 10));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x60, 0x61, 0x51, 0x61, 0x51, 0x60, 0x61, 0x51, 0x61, 0x51, 0x60, 0x61, 0x51, 0x67, 0x02, 0x02, 0x04, 0x02, 0x02, 0x04, 0x02, 0x02, 0x04, 0x61, 0x52, 0x67, 0x60, 0x35, 0x01, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1024u, 1056u, 101>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            aot::mstore_c<traits, 928u, 960u, 91>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 608u, 640u, 60>(ctx, gas);
            uint256_t const t4 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t5 = aot::mload_c<traits, 576u, 608u, 57>(ctx, gas);
            uint256_t const t6 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t7 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t8 = aot::mul(uint256_t{0xde0b6b3a7640000ull}, t7);
            uint256_t const t9 = aot::mul(t8, uint256_t{0x3ull});
            uint256_t const t10 = aot::udiv(t9, t6);
            uint256_t const t11 = aot::mul(t10, t5);
            uint256_t const t12 = aot::mul(t11, uint256_t{0x3ull});
            uint256_t const t13 = aot::udiv(t12, t4);
            uint256_t const t14 = aot::mul(t13, t3);
            uint256_t const t15 = aot::mul(t14, uint256_t{0x3ull});
            uint256_t const t16 = aot::udiv(t15, t2);
            aot::mstore_c<traits, 704u, 736u, 70>(ctx, gas, t16);
            uint256_t const t17 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t18 = t17 + uint256_t{0xde0b6b3a7640000ull};
            aot::mstore_c<traits, 736u, 768u, 73>(ctx, gas, t18);
            uint256_t const t19 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t20 = aot::mload_c<traits, 736u, 768u, 73>(ctx, gas);
            uint256_t const t21 = aot::from_bool(t19 < t20);
            bool const j47 = aot::nonzero(t21);
            if (j47) { MONAD_AOT_TAIL return b_1307<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_12f3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12f3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x51, 0x61, 0x51, 0x03, 0x01, 0x61, 0x52, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x51, 0x61, 0x51, 0x03, 0x01, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 736u, 768u, 73>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t3 = t2 - t1;
            uint256_t const t4 = t3 + uint256_t{0x1ull};
            aot::mstore_c<traits, 736u, 768u, 73>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_1318<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1307(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x61, 0x51, 0x61, 0x51, 0x03, 0x01, 0x61, 0x52}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x61, 0x51, 0x61, 0x51, 0x03, 0x01, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 736u, 768u, 73>(ctx, gas);
            uint256_t const t3 = t2 - t1;
            uint256_t const t4 = t3 + uint256_t{0x1ull};
            aot::mstore_c<traits, 736u, 768u, 73>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_1318<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1318(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x61, 0x61, 0x51, 0x60, 0x35, 0x61, 0x51, 0x60, 0x35, 0x61, 0x51, 0x67, 0x02, 0x04, 0x02, 0x04, 0x02, 0x02, 0x04, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x02, 0x04, 0x61, 0x52, 0x67, 0x61, 0x51, 0x61, 0x51, 0x02, 0x04, 0x61, 0x51, 0x60, 0x61, 0x51, 0x02, 0x04, 0x67, 0x61, 0x51, 0x61, 0x51, 0x02, 0x04, 0x61, 0x51, 0x01, 0x01, 0x03, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x01, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 0, 8));
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x61, 0x61, 0x51, 0x60, 0x35, 0x61, 0x51, 0x60, 0x35, 0x61, 0x51, 0x67, 0x02, 0x04, 0x02, 0x04, 0x02, 0x02, 0x04, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x02, 0x04, 0x61, 0x52, 0x67, 0x61, 0x51, 0x61, 0x51, 0x02, 0x04, 0x61, 0x51, 0x60, 0x61, 0x51, 0x02, 0x04, 0x67, 0x61, 0x51, 0x61, 0x51, 0x02, 0x04, 0x61, 0x51, 0x01, 0x01, 0x03, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x01, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::mload_c<traits, 736u, 768u, 73>(ctx, gas);
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t4 = aot::mload_c<traits, 736u, 768u, 73>(ctx, gas);
            uint256_t const t5 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t6 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t7 = aot::mul(uint256_t{0xde0b6b3a7640000ull}, t6);
            uint256_t const t8 = aot::udiv(t7, t5);
            uint256_t const t9 = aot::mul(t8, t4);
            uint256_t const t10 = aot::udiv(t9, t3);
            uint256_t const t11 = aot::mul(t10, t2);
            uint256_t const t12 = aot::mul(t11, uint256_t{0x2710ull});
            uint256_t const t13 = aot::udiv(t12, t1);
            aot::mstore_c<traits, 768u, 800u, 76>(ctx, gas, t13);
            uint256_t const t14 = aot::mload_c<traits, 736u, 768u, 73>(ctx, gas);
            uint256_t const t15 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t16 = aot::mul(uint256_t{0x53444835ec580000ull}, t15);
            uint256_t const t17 = aot::udiv(t16, t14);
            aot::mstore_c<traits, 800u, 832u, 79>(ctx, gas, t17);
            uint256_t const t18 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t19 = aot::mload_c<traits, 800u, 832u, 79>(ctx, gas);
            uint256_t const t20 = aot::mul(t19, t18);
            uint256_t const t21 = aot::udiv(t20, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t22 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t23 = aot::mload_c<traits, 768u, 800u, 76>(ctx, gas);
            uint256_t const t24 = aot::mul(t23, uint256_t{0x3ull});
            uint256_t const t25 = aot::udiv(t24, t22);
            uint256_t const t26 = aot::mload_c<traits, 800u, 832u, 79>(ctx, gas);
            uint256_t const t27 = aot::mload_c<traits, 640u, 672u, 63>(ctx, gas);
            uint256_t const t28 = aot::mul(t27, t26);
            uint256_t const t29 = aot::udiv(t28, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t30 = aot::mload_c<traits, 640u, 672u, 63>(ctx, gas);
            uint256_t const t31 = t30 + t29;
            uint256_t const t32 = t31 + t25;
            uint256_t const t33 = t32 - t21;
            aot::mstore_c<traits, 832u, 864u, 82>(ctx, gas, t33);
            uint256_t const t34 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t35 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t36 = aot::mload_c<traits, 640u, 672u, 63>(ctx, gas);
            uint256_t const t37 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t38 = t37 + t36;
            uint256_t const t39 = aot::mul(t35, t38);
            uint256_t const t40 = aot::from_bool(!aot::nonzero(t38));
            uint256_t const t41 = aot::udiv(t39, t38);
            uint256_t const t42 = aot::from_bool(t41 == t35);
            uint256_t const t43 = t42 | t40;
            uint256_t const t44 = aot::from_bool(!aot::nonzero(t43));
            bool const j83 = aot::nonzero(t44);
            top[1] = t34;
            top[2] = t35;
            top[3] = t38;
            top[4] = t39;
            top += 4;
            if (j83) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_13ba<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_13ba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            aot::mstore_c<traits, 864u, 896u, 85>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t4 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t5 = aot::mul(t3, t4);
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t7 = aot::udiv(t5, t4);
            uint256_t const t8 = aot::from_bool(t7 == t3);
            uint256_t const t9 = t8 | t6;
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            bool const j26 = aot::nonzero(t10);
            top[-3] = t2;
            top[-2] = t3;
            top[-1] = t4;
            top[0] = t5;
            if (j26) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_13df<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_13df(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x52, 0x67, 0x61, 0x51, 0x11, 0x15, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x52, 0x67, 0x61, 0x51, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            aot::mstore_c<traits, 896u, 928u, 88>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t3 = aot::from_bool(uint256_t{0xde0b6b3a763ffffull} < t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j13 = aot::nonzero(t4);
            top += -4;
            if (j13) { MONAD_AOT_TAIL return b_1454<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_13fb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_13fb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x67, 0x61, 0x51, 0x03, 0x67, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x04, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 0, 11));
            if (MONAD_UNLIKELY(top - bottom > 1013)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x67, 0x61, 0x51, 0x03, 0x67, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x04, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t4 = t3 - uint256_t{0xde0b6b3a7640000ull};
            uint256_t const t5 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t6 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t7 = aot::mload_c<traits, 768u, 800u, 76>(ctx, gas);
            uint256_t const t8 = aot::udiv(t7, t6);
            uint256_t const t9 = aot::mul(t5, t8);
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t8));
            uint256_t const t11 = aot::udiv(t9, t8);
            uint256_t const t12 = aot::from_bool(t11 == t5);
            uint256_t const t13 = t12 | t10;
            uint256_t const t14 = aot::from_bool(!aot::nonzero(t13));
            bool const j29 = aot::nonzero(t14);
            top[1] = t1;
            top[2] = t2;
            top[3] = t4;
            top[4] = uint256_t{0xde0b6b3a7640000ull};
            top[5] = t5;
            top[6] = t8;
            top[7] = t9;
            top += 7;
            if (j29) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1437<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1437(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x02, 0x04, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x02, 0x04, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = aot::mul(t1, s4);
            uint256_t const &s5 = top[-5];
            uint256_t const t3 = aot::udiv(t2, s5);
            uint256_t const &s6 = top[-6];
            uint256_t const t4 = s6 - t3;
            uint256_t const t5 = aot::from_bool(s6 < t4);
            bool const j14 = aot::nonzero(t5);
            top[-5] = t3;
            top[-4] = t4;
            top += -4;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1448<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1448(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 896u, 928u, 88>(ctx, gas, s0);
            top += -3;
            MONAD_AOT_TAIL return b_14aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1454(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x67, 0x03, 0x67, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x04, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 0, 11));
            if (MONAD_UNLIKELY(top - bottom > 1013)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x67, 0x03, 0x67, 0x61, 0x51, 0x61, 0x51, 0x61, 0x51, 0x04, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            uint256_t const t4 = uint256_t{0xde0b6b3a7640000ull} - t3;
            uint256_t const t5 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t6 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t7 = aot::mload_c<traits, 768u, 800u, 76>(ctx, gas);
            uint256_t const t8 = aot::udiv(t7, t6);
            uint256_t const t9 = aot::mul(t5, t8);
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t8));
            uint256_t const t11 = aot::udiv(t9, t8);
            uint256_t const t12 = aot::from_bool(t11 == t5);
            uint256_t const t13 = t12 | t10;
            uint256_t const t14 = aot::from_bool(!aot::nonzero(t13));
            bool const j30 = aot::nonzero(t14);
            top[1] = t1;
            top[2] = t2;
            top[3] = t4;
            top[4] = uint256_t{0xde0b6b3a7640000ull};
            top[5] = t5;
            top[6] = t8;
            top[7] = t9;
            top += 7;
            if (j30) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1491<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1491(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x02, 0x04, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x02, 0x04, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = aot::mul(t1, s4);
            uint256_t const &s5 = top[-5];
            uint256_t const t3 = aot::udiv(t2, s5);
            uint256_t const &s6 = top[-6];
            uint256_t const t4 = s6 + t3;
            uint256_t const t5 = aot::from_bool(t4 < s6);
            bool const j14 = aot::nonzero(t5);
            top[-5] = t3;
            top[-4] = t4;
            top += -4;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_14a2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14a2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 896u, 928u, 88>(ctx, gas, s0);
            top += -3;
            MONAD_AOT_TAIL return b_14aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_14aa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 864u, 896u, 85>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t1 < t2);
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_14cc<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_14b8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14b8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x03, 0x60, 0x1c, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x03, 0x60, 0x1c, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 864u, 896u, 85>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
            uint256_t const t3 = t2 - t1;
            uint256_t const t4 = aot::shr_c<1>(t3);
            aot::mstore_c<traits, 672u, 704u, 66>(ctx, gas, t4);
            MONAD_AOT_TAIL return b_14da<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_14cc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x03, 0x61, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x03, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 864u, 896u, 85>(ctx, gas);
            uint256_t const t3 = t2 - t1;
            aot::mstore_c<traits, 672u, 704u, 66>(ctx, gas, t3);
            MONAD_AOT_TAIL return b_14da<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_14da(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 928u, 960u, 91>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t1 < t2);
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_14f9<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_14e8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14e8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x03, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x03, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 928u, 960u, 91>(ctx, gas);
            uint256_t const t3 = t2 - t1;
            aot::mstore_c<traits, 960u, 992u, 94>(ctx, gas, t3);
            MONAD_AOT_TAIL return b_1507<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_14f9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x03, 0x61, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x61, 0x51, 0x03, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 928u, 960u, 91>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t3 = t2 - t1;
            aot::mstore_c<traits, 960u, 992u, 94>(ctx, gas, t3);
            MONAD_AOT_TAIL return b_1507<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1507(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x80, 0x66, 0x81, 0x18, 0x82, 0x66, 0x11, 0x02, 0x18, 0x90, 0x50, 0x65, 0x61, 0x51, 0x02, 0x10, 0x15, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x80, 0x66, 0x81, 0x18, 0x82, 0x66, 0x11, 0x02, 0x18, 0x90, 0x50, 0x65, 0x61, 0x51, 0x02, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t2 = t1 ^ uint256_t{0x2386f26fc10000ull};
            uint256_t const t3 = aot::from_bool(t1 < uint256_t{0x2386f26fc10000ull});
            uint256_t const t4 = aot::mul(t3, t2);
            uint256_t const t5 = t4 ^ t1;
            uint256_t const t6 = aot::mload_c<traits, 960u, 992u, 94>(ctx, gas);
            uint256_t const t7 = aot::mul(t6, uint256_t{0x5af3107a4000ull});
            uint256_t const t8 = aot::from_bool(t7 < t5);
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            bool const j21 = aot::nonzero(t9);
            if (j21) { MONAD_AOT_TAIL return b_1609<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1537<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1537(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x60, 0x90}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x60, 0x90}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x3ull};
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_153b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_153b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x60, 0x1b, 0x61, 0x01, 0x51, 0x61, 0x52, 0x61, 0x51, 0x67, 0x61, 0x51, 0x02, 0x04, 0x61, 0x52, 0x66, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x60, 0x1b, 0x61, 0x01, 0x51, 0x61, 0x52, 0x61, 0x51, 0x67, 0x61, 0x51, 0x02, 0x04, 0x61, 0x52, 0x66, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const t2 = uint256_t{0x220ull} + t1;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            aot::mstore_c<traits, 1056u, 1088u, 104>(ctx, gas, t3);
            uint256_t const t4 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            uint256_t const t5 = aot::mload_c<traits, 1056u, 1088u, 104>(ctx, gas);
            uint256_t const t6 = aot::mul(t5, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t7 = aot::udiv(t6, t4);
            aot::mstore_c<traits, 992u, 1024u, 98>(ctx, gas, t7);
            uint256_t const t8 = aot::mload_c<traits, 992u, 1024u, 98>(ctx, gas);
            uint256_t const t9 = aot::from_bool(t8 < uint256_t{0x2386f26fc0ffffull});
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            bool const j24 = aot::nonzero(t10);
            if (j24) { MONAD_AOT_TAIL return b_1577<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1572<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1572(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_1588<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1577(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x68, 0x61, 0x51, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x68, 0x61, 0x51, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 992u, 1024u, 98>(ctx, gas);
            uint256_t const t2 = aot::from_bool(uint256_t{0x6bc75e2d63100000ull, 0x5ull, 0x0ull, 0x0ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_1588<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1588(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j2 = aot::nonzero(s0);
            top += -1;
            if (j2) { MONAD_AOT_TAIL return b_15f1<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_158d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_158d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1088u, 1120u, 107>(ctx, gas, uint256_t{0x12ull});
            aot::mstore_c<traits, 1120u, 1152u, 110>(ctx, gas, uint256_t{0x0ull, 0x695d000000000000ull, 0x616c75657320785bull, 0x556e736166652076ull});
            uint256_t const t1 = aot::mload_c<traits, 1088u, 1120u, 107>(ctx, gas);
            uint256_t const t2 = uint256_t{0x460ull} + t1;
            uint256_t const t3 = uint256_t{0x0ull} - t1;
            uint256_t const t4 = t3 & uint256_t{0x1full};
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t2, &t5, &t4);
            gas = ctx->gas_remaining;
            aot::mstore_c<traits, 1024u, 1056u, 101>(ctx, gas, uint256_t{0x8c379a0ull});
            aot::mstore_c<traits, 1056u, 1088u, 104>(ctx, gas, uint256_t{0x20ull});
            uint256_t const t6 = aot::mload_c<traits, 1088u, 1120u, 107>(ctx, gas);
            uint256_t const t7 = t6 + uint256_t{0x1full};
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t9 = uint256_t{0x44ull} + t8;
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x41cull}, t9);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_15f1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j7) { MONAD_AOT_TAIL return b_153b<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_15fc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_15fc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x60, 0x61, 0x61, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x60, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-3] = uint256_t{0x20ull};
            top[-2] = uint256_t{0x2a0ull};
            top += -2;
            MONAD_AOT_TAIL return b_167a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1609(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j7) { MONAD_AOT_TAIL return b_1293<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1614<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1614(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1024u, 1056u, 101>(ctx, gas, uint256_t{0x10ull});
            aot::mstore_c<traits, 1056u, 1088u, 104>(ctx, gas, uint256_t{0x0ull, 0x0ull, 0x636f6e7665726765ull, 0x446964206e6f7420ull});
            uint256_t const t1 = aot::mload_c<traits, 1024u, 1056u, 101>(ctx, gas);
            uint256_t const t2 = uint256_t{0x420ull} + t1;
            uint256_t const t3 = uint256_t{0x0ull} - t1;
            uint256_t const t4 = t3 & uint256_t{0x1full};
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t2, &t5, &t4);
            gas = ctx->gas_remaining;
            aot::mstore_c<traits, 960u, 992u, 94>(ctx, gas, uint256_t{0x8c379a0ull});
            aot::mstore_c<traits, 992u, 1024u, 98>(ctx, gas, uint256_t{0x20ull});
            uint256_t const t6 = aot::mload_c<traits, 1024u, 1056u, 101>(ctx, gas);
            uint256_t const t7 = t6 + uint256_t{0x1full};
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t9 = uint256_t{0x44ull} + t8;
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x3dcull}, t9);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_167a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
        [[gnu::noinline]] void b_167c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0x754b76b3ull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_19cb<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1688<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1688(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xc4ull});
            bool const j4 = aot::nonzero(t2);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1690<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1690(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x67, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x67, 0x60, 0x35, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x16345785d8a0000ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_16a7<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_16a2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_16a2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_16bc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_16a7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x6d, 0x60, 0x35, 0x11, 0x15}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x6d, 0x60, 0x35, 0x11, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0x38c15b0a00000000ull, 0x314dc6448d93ull, 0x0ull, 0x0ull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_16bc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_16bc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_16c2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_16c2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x60, 0x35, 0x60, 0x35, 0x60, 0x35, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}, 0, 8));
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x60, 0x35, 0x60, 0x35, 0x60, 0x35, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const t4 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t5 = aot::mul(t4, uint256_t{0x1bull});
            uint256_t const t6 = aot::udiv(t5, uint256_t{0x1bull});
            uint256_t const t7 = t6 ^ t4;
            bool const j17 = aot::nonzero(t7);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top[4] = t4;
            top[5] = t5;
            top += 5;
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_16dc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_16dc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_16f1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_16f1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x35, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x35, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x44ull});
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
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1709<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1709(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1738<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1738(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j18) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_176f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_176f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1784<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1784(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_179c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_179c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x67, 0x60, 0x35, 0x01, 0x0a, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x67, 0x60, 0x35, 0x01, 0x0a, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const t3 = t2 + uint256_t{0xde0b6b3a7640000ull};
            uint256_t const t4 = aot::exp_c<0x2u>(t3);
            uint256_t const t5 = t1 + t4;
            uint256_t const t6 = aot::from_bool(t5 < t1);
            bool const j18 = aot::nonzero(t6);
            top[-3] = t1;
            top[-2] = t4;
            top[-1] = t5;
            top += -1;
            if (j18) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_17bb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_17bb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x67, 0x6e, 0x60, 0x60, 0x51, 0x0a, 0x04, 0x67, 0x60, 0x35, 0x60, 0x1b, 0x01, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 3, 6));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x67, 0x6e, 0x60, 0x60, 0x51, 0x0a, 0x04, 0x67, 0x60, 0x35, 0x60, 0x1b, 0x01, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::exp_c<0x2u>(t1);
            uint256_t const t3 = aot::udiv(t2, uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull});
            uint256_t const t4 = aot::calldataload(ctx, uint256_t{0xa4ull});
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
            if (j30) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_17ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_17ff(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_180e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_180e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x52, 0x61, 0x60, 0x60, 0x35, 0x0a, 0x60, 0x35, 0x02, 0x04, 0x60, 0x52, 0x60, 0x51, 0x6e, 0x60, 0x35, 0x60, 0x51, 0x60, 0x35, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 3, 7));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x52, 0x61, 0x60, 0x60, 0x35, 0x0a, 0x60, 0x35, 0x02, 0x04, 0x60, 0x52, 0x60, 0x51, 0x6e, 0x60, 0x35, 0x60, 0x51, 0x60, 0x35, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 50;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const t2 = aot::exp_c<0x2u>(t1);
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t4 = aot::mul(t3, t2);
            uint256_t const t5 = aot::udiv(t4, uint256_t{0x2710ull});
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t5);
            uint256_t const t6 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t7 = aot::calldataload(ctx, uint256_t{0x64ull});
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
            if (j39) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1852<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1852(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_186a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_186a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1879<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1879(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            uint256_t const t4 = aot::calldataload(ctx, uint256_t{0x64ull});
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
            if (j32) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_18b2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18b2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_18ca<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18ca(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_18d9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18d9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_18ed<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18ed(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_18fa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18fa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j16) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_191d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_191d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x04, 0x60, 0x52, 0x60, 0x51, 0x60, 0x35, 0x60, 0x51, 0x6e, 0x60, 0x35, 0x60, 0x51, 0x60, 0x35, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 3, 9));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x04, 0x60, 0x52, 0x60, 0x51, 0x60, 0x35, 0x60, 0x51, 0x6e, 0x60, 0x35, 0x60, 0x51, 0x60, 0x35, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::udiv(s0, s2);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t4 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t5 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const t6 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t7 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t8 = aot::mul(t6, t7);
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t7));
            uint256_t const t10 = aot::udiv(t8, t7);
            uint256_t const t11 = aot::from_bool(t10 == t6);
            uint256_t const t12 = t11 | t9;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t12));
            bool const j31 = aot::nonzero(t13);
            top[-2] = t2;
            top[-1] = t3;
            top[0] = t4;
            top[1] = uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull};
            top[2] = t5;
            top[3] = t6;
            top[4] = t7;
            top[5] = t8;
            top += 5;
            if (j31) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1955<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1955(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_196d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_196d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_197c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_197c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1990<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1990(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x35, 0x80, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x35, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_199d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_199d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j16) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_19c0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_19c0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x04, 0x60, 0x52, 0x60, 0x60, 0xf3}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x04, 0x60, 0x52, 0x60, 0x60, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::udiv(s0, s2);
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t1);
            aot::finish(ctx, gas, StatusCode::Success, uint256_t{0xc0ull}, uint256_t{0x40ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_19cb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0xf42c56c2ull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_19f6<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_19d7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_19d7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x24ull});
            bool const j4 = aot::nonzero(t2);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_19df<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_19df(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x35, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x35, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t1);
            top[1] = uint256_t{0x20ull};
            top[2] = uint256_t{0x19f1ull};
            top[3] = uint256_t{0x160ull};
            top += 3;
            MONAD_AOT_TAIL return b_24aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_19f6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0xbad1dc26ull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1a23<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1a02<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a02(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x64ull});
            bool const j4 = aot::nonzero(t2);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1a0a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a0a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x60, 0x61, 0x37, 0x61, 0x61, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x60, 0x61, 0x37, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const k4_0 = uint256_t{0x160ull};
            uint256_t const k4_1 = uint256_t{0x4ull};
            uint256_t const k4_2 = uint256_t{0x60ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k4_0, &k4_1, &k4_2);
            gas = ctx->gas_remaining;
            top[1] = uint256_t{0x20ull};
            top[2] = uint256_t{0x1a1eull};
            top[3] = uint256_t{0x200ull};
            top += 3;
            MONAD_AOT_TAIL return b_26b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a1e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0xf3}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::finish(ctx, gas, StatusCode::Success, uint256_t{0x200ull}, s0);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a23(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0xfa18042dull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1a55<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1a2f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a2f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x84ull});
            bool const j4 = aot::nonzero(t2);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1a37<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a37(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x60, 0x60, 0x37, 0x60, 0x35, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x60, 0x60, 0x37, 0x60, 0x35, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const k4_0 = uint256_t{0x40ull};
            uint256_t const k4_1 = uint256_t{0x4ull};
            uint256_t const k4_2 = uint256_t{0x60ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k4_0, &k4_1, &k4_2);
            gas = ctx->gas_remaining;
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x64ull});
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t1);
            top[1] = uint256_t{0x20ull};
            top[2] = uint256_t{0x1a50ull};
            top[3] = uint256_t{0x100ull};
            top += 3;
            MONAD_AOT_TAIL return b_272c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a50(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0xf3}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::finish(ctx, gas, StatusCode::Success, uint256_t{0x100ull}, s0);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a55(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 ^ uint256_t{0x81d18d87ull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a80); }
            MONAD_AOT_TAIL return b_1a61<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a61(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x24ull});
            bool const j4 = aot::nonzero(t2);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1a69<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a69(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x35, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x35, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t1);
            top[1] = uint256_t{0x20ull};
            top[2] = uint256_t{0x1a7bull};
            top[3] = uint256_t{0x120ull};
            top += 3;
            MONAD_AOT_TAIL return b_2854<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a7b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0xf3}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::finish(ctx, gas, StatusCode::Success, uint256_t{0x120ull}, s0);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a86(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x52, 0x60, 0x51, 0x60, 0x52, 0x60, 0x51, 0x60, 0x52, 0x60, 0x51, 0x61, 0x52, 0x60, 0x51, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x52, 0x60, 0x51, 0x60, 0x52, 0x60, 0x51, 0x60, 0x52, 0x60, 0x51, 0x61, 0x52, 0x60, 0x51, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t2);
            uint256_t const t3 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t3);
            uint256_t const t4 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            aot::mstore_c<traits, 256u, 288u, 27>(ctx, gas, t4);
            uint256_t const t5 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t6 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t7 = aot::from_bool(t6 < t5);
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j24 = aot::nonzero(t8);
            if (j24) { MONAD_AOT_TAIL return b_1ab9<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1aac<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1aac(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x60, 0x52, 0x61, 0x51, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x60, 0x52, 0x61, 0x51, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 256u, 288u, 27>(ctx, gas);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_1ab9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ab9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t2 < t1);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j8 = aot::nonzero(t4);
            if (j8) { MONAD_AOT_TAIL return b_1ada<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1ac6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ac6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x61, 0x52, 0x60, 0x51, 0x60, 0x52, 0x61, 0x51, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x61, 0x52, 0x60, 0x51, 0x60, 0x52, 0x61, 0x51, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            aot::mstore_c<traits, 256u, 288u, 27>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t2);
            uint256_t const t3 = aot::mload_c<traits, 256u, 288u, 27>(ctx, gas);
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t3);
            MONAD_AOT_TAIL return b_1ada<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ada(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t2 < t1);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j8 = aot::nonzero(t4);
            if (j8) { MONAD_AOT_TAIL return b_1afb<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1ae7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ae7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x61, 0x52, 0x60, 0x51, 0x60, 0x52, 0x61, 0x51, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x61, 0x52, 0x60, 0x51, 0x60, 0x52, 0x61, 0x51, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            aot::mstore_c<traits, 256u, 288u, 27>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t2);
            uint256_t const t3 = aot::mload_c<traits, 256u, 288u, 27>(ctx, gas);
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t3);
            MONAD_AOT_TAIL return b_1afb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1afb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x81, 0x52, 0x60, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x51, 0x60, 0x82, 0x01, 0x52, 0x50, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x81, 0x52, 0x60, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x51, 0x60, 0x82, 0x01, 0x52, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, t1);
            uint256_t const t2 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t3 = s0 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t5 = s0 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 10935)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b30(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x60, 0x81, 0x11, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x60, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t2 = aot::from_bool(uint256_t{0x2ull} < t1);
            bool const j6 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1b3c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b3c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1b, 0x61, 0x01, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1b, 0x61, 0x01, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const t2 = uint256_t{0x160ull} + t1;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = aot::mul(t3, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t5 = aot::udiv(t4, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t6 = t5 ^ t3;
            bool const j14 = aot::nonzero(t6);
            top[0] = t3;
            top[1] = t4;
            top += 1;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1b60<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b60(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1b6c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b6c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x66, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x66, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 512u, 544u, 51>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 512u, 544u, 51>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t2 < uint256_t{0x2386f26fc10000ull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j15 = aot::nonzero(t4);
            top += -2;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8e); }
            MONAD_AOT_TAIL return b_1b89<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b89(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b9f);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ba4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 576u, 608u, 57>(ctx, gas, uint256_t{0x12ull});
            aot::mstore_c<traits, 608u, 640u, 60>(ctx, gas, uint256_t{0x0ull, 0x695d000000000000ull, 0x616c75657320785bull, 0x556e736166652076ull});
            uint256_t const t1 = aot::mload_c<traits, 576u, 608u, 57>(ctx, gas);
            uint256_t const t2 = uint256_t{0x260ull} + t1;
            uint256_t const t3 = uint256_t{0x0ull} - t1;
            uint256_t const t4 = t3 & uint256_t{0x1full};
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t2, &t5, &t4);
            gas = ctx->gas_remaining;
            aot::mstore_c<traits, 512u, 544u, 51>(ctx, gas, uint256_t{0x8c379a0ull});
            aot::mstore_c<traits, 544u, 576u, 54>(ctx, gas, uint256_t{0x20ull});
            uint256_t const t6 = aot::mload_c<traits, 576u, 608u, 57>(ctx, gas);
            uint256_t const t7 = t6 + uint256_t{0x1full};
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t9 = uint256_t{0x44ull} + t8;
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x21cull}, t9);
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c13(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x61, 0x51, 0x60, 0x81, 0x04, 0x90, 0x50, 0x61, 0x52, 0x67, 0x61, 0x52, 0x5f, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x5f, 0x61, 0x51, 0x60, 0x81, 0x11, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x61, 0x51, 0x60, 0x81, 0x04, 0x90, 0x50, 0x61, 0x52, 0x67, 0x61, 0x52, 0x5f, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x52, 0x5f, 0x61, 0x51, 0x60, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t2 = aot::udiv(t1, uint256_t{0x3ull});
            aot::mstore_c<traits, 544u, 576u, 54>(ctx, gas, t2);
            aot::mstore_c<traits, 576u, 608u, 57>(ctx, gas, uint256_t{0xde0b6b3a7640000ull});
            aot::mstore_c<traits, 608u, 640u, 60>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t3 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            aot::mstore_c<traits, 640u, 672u, 63>(ctx, gas, t3);
            uint256_t const t4 = aot::mload_c<traits, 384u, 416u, 39>(ctx, gas);
            aot::mstore_c<traits, 672u, 704u, 66>(ctx, gas, t4);
            uint256_t const t5 = aot::mload_c<traits, 416u, 448u, 42>(ctx, gas);
            aot::mstore_c<traits, 704u, 736u, 70>(ctx, gas, t5);
            uint256_t const t6 = aot::mload_c<traits, 480u, 512u, 48>(ctx, gas);
            uint256_t const t7 = aot::from_bool(uint256_t{0x2ull} < t6);
            bool const j36 = aot::nonzero(t7);
            top[-1] = uint256_t{0x0ull};
            top[0] = t6;
            if (j36) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1c5a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c5a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1b, 0x61, 0x01, 0x52, 0x61, 0x51, 0x60, 0x52, 0x61, 0x51, 0x60, 0x52, 0x61, 0x51, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1b, 0x61, 0x01, 0x52, 0x61, 0x51, 0x60, 0x52, 0x61, 0x51, 0x60, 0x52, 0x61, 0x51, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const t2 = uint256_t{0x280ull} + t1;
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t2, s1);
            uint256_t const t3 = aot::mload_c<traits, 640u, 672u, 63>(ctx, gas);
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t3);
            uint256_t const t4 = aot::mload_c<traits, 672u, 704u, 66>(ctx, gas);
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, t4);
            uint256_t const t5 = aot::mload_c<traits, 704u, 736u, 70>(ctx, gas);
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t5);
            top[-1] = uint256_t{0x1c81ull};
            top[0] = uint256_t{0x2e0ull};
            MONAD_AOT_TAIL return b_1a86<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d0f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x81, 0x11, 0x61, 0x57}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x2ull} < s0);
            bool const j6 = aot::nonzero(t1);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1d19<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d19(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1b, 0x61, 0x01, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 1, 6));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1b, 0x61, 0x01, 0x51, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const t2 = uint256_t{0x280ull} + t1;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            aot::mstore_c<traits, 800u, 832u, 79>(ctx, gas, t3);
            uint256_t const t4 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t5 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t6 = aot::mul(t4, t5);
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const t8 = aot::udiv(t6, t5);
            uint256_t const t9 = aot::from_bool(t8 == t4);
            uint256_t const t10 = t9 | t7;
            uint256_t const t11 = aot::from_bool(!aot::nonzero(t10));
            bool const j24 = aot::nonzero(t11);
            top[0] = t4;
            top[1] = t5;
            top[2] = t6;
            top += 2;
            if (j24) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1d3d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d3d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 800u, 832u, 79>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0x3ull});
            uint256_t const t3 = aot::udiv(t2, uint256_t{0x3ull});
            uint256_t const t4 = t3 ^ t1;
            bool const j15 = aot::nonzero(t4);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = t2;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1d53<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d53(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1d5b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d5b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 544u, 576u, 54>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 608u, 640u, 60>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 800u, 832u, 79>(ctx, gas);
            uint256_t const t4 = t2 + t3;
            uint256_t const t5 = aot::from_bool(t4 < t2);
            bool const j20 = aot::nonzero(t5);
            top[-1] = t2;
            top[0] = t3;
            top[1] = t4;
            top += 1;
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1d78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d78(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x01, 0x81, 0x81, 0x18, 0x61, 0x57}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x01, 0x81, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 608u, 640u, 60>(ctx, gas, s0);
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = uint256_t{0x1ull} + s3;
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = t1 ^ s4;
            bool const j12 = aot::nonzero(t2);
            top[-3] = t1;
            top += -3;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1cf9); }
            MONAD_AOT_TAIL return b_1d8a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d8a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x5f, 0x60, 0x90}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x5f, 0x60, 0x90}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-1] = uint256_t{0x2ull};
            top[0] = uint256_t{0x0ull};
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1d90);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1da6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1b, 0x61, 0x01, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1b, 0x61, 0x01, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const t2 = uint256_t{0x280ull} + t1;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const &s1 = top[-1];
            uint256_t const t4 = aot::mul(s1, t3);
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t6 = aot::udiv(t4, t3);
            uint256_t const t7 = aot::from_bool(t6 == s1);
            uint256_t const t8 = t7 | t5;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            bool const j18 = aot::nonzero(t9);
            top[0] = t3;
            top[1] = t4;
            top += 1;
            if (j18) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1dbe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dbe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(s0, uint256_t{0x3ull});
            uint256_t const t2 = aot::udiv(t1, uint256_t{0x3ull});
            uint256_t const t3 = t2 ^ s0;
            bool const j13 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1dd0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dd0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1ddc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ddc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x01, 0x81, 0x81, 0x18, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x60, 0x01, 0x81, 0x81, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 576u, 608u, 57>(ctx, gas, t1);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = uint256_t{0x1ull} + s2;
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = t2 ^ s3;
            bool const j15 = aot::nonzero(t3);
            top[-2] = t2;
            top += -2;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1d90); }
            MONAD_AOT_TAIL return b_1df1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1df1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x61, 0x36, 0x61, 0x37, 0x5f, 0x60, 0x90}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x61, 0x36, 0x61, 0x37, 0x5f, 0x60, 0x90}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const k5_0 = uint256_t{0x300ull};
            uint256_t const k5_2 = uint256_t{0x180ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &k5_0, &t1, &k5_2);
            gas = ctx->gas_remaining;
            top[-1] = uint256_t{0xffull};
            top[0] = uint256_t{0x0ull};
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1dff);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e25(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(s0, uint256_t{0x3ull});
            uint256_t const t2 = aot::udiv(t1, uint256_t{0x3ull});
            uint256_t const t3 = t2 ^ s0;
            bool const j13 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1e37<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e37(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1e43<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e43(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 832u, 864u, 82>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 608u, 640u, 60>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t4 = t2 + t3;
            uint256_t const t5 = aot::from_bool(t4 < t2);
            bool const j20 = aot::nonzero(t5);
            top[-1] = t2;
            top[0] = t3;
            top[1] = t4;
            top += 1;
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1e60<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e60(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x01, 0x81, 0x81, 0x10, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x01, 0x81, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 864u, 896u, 85>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0xde0b6b3a7640000ull};
            uint256_t const t3 = aot::from_bool(t2 < t1);
            bool const j15 = aot::nonzero(t3);
            top[-2] = t1;
            top[-1] = t2;
            top += -1;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1e7e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e7e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 896u, 928u, 88>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t1 < t2);
            bool const j10 = aot::nonzero(t3);
            top += -2;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1ebc); }
            MONAD_AOT_TAIL return b_1e91<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e91(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
            uint256_t const t3 = t1 - t2;
            uint256_t const t4 = aot::from_bool(t1 < t3);
            bool const j11 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1ea3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ea3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1eb2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1eb2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x52, 0x61, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 896u, 928u, 88>(ctx, gas, s0);
            top += -2;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1ee4);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ecf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1ede<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ede(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x52}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 896u, 928u, 88>(ctx, gas, s0);
            top += -2;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1ee4);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f05(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1f11<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f11(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            uint256_t const t2 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
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
            if (j22) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1f2c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f2c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1f3a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f3a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            uint256_t const t2 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
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
            if (j22) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1f55<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f55(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1f69<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f69(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 288u, 320u, 30>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1f75<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f75(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 928u, 960u, 91>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0x1bc16d674ec80000ull});
            uint256_t const t4 = aot::udiv(t3, uint256_t{0x1bc16d674ec80000ull});
            uint256_t const t5 = t4 ^ t2;
            bool const j20 = aot::nonzero(t5);
            top[-1] = t2;
            top[0] = t3;
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1fa0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fa0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 896u, 928u, 88>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1fac<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fac(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1fcd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fcd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 960u, 992u, 94>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t3 = aot::udiv(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = t3 ^ t1;
            bool const j15 = aot::nonzero(t4);
            top[-1] = t1;
            top[0] = t2;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_1ff3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ff3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 864u, 896u, 85>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 960u, 992u, 94>(ctx, gas);
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
            if (j19) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_200d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_200d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_201b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_201b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 928u, 960u, 91>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 + t1;
            uint256_t const t3 = aot::from_bool(t2 < s0);
            bool const j13 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = t2;
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_202d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_202d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 992u, 1024u, 98>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 960u, 992u, 94>(ctx, gas);
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
            if (j23) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_204d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_204d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x10, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1024u, 1056u, 101>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1024u, 1056u, 101>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 992u, 1024u, 98>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t2 < t1);
            bool const j12 = aot::nonzero(t3);
            top += -3;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2080); }
            MONAD_AOT_TAIL return b_2062<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2062(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 992u, 1024u, 98>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1024u, 1056u, 101>(ctx, gas);
            uint256_t const t3 = t1 - t2;
            uint256_t const t4 = aot::from_bool(t1 < t3);
            bool const j11 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2074<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2074(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 992u, 1024u, 98>(ctx, gas, s0);
            top += -3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2093);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_20a2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 1056u, 1088u, 104>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 928u, 960u, 91>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 1056u, 1088u, 104>(ctx, gas);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j16 = aot::nonzero(t4);
            top[-1] = t2;
            top[0] = t3;
            if (j16) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_20bb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_20bb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 1088u, 1120u, 107>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 992u, 1024u, 98>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t4 = aot::mul(t3, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t5 = aot::udiv(t4, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t6 = t5 ^ t3;
            bool const j22 = aot::nonzero(t6);
            top[-1] = t2;
            top[0] = t3;
            top[1] = t4;
            top += 1;
            if (j22) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_20ea<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_20ea(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_20f6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_20f6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1056u, 1088u, 104>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2104<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2104(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            uint256_t const t2 = aot::mload_c<traits, 1088u, 1120u, 107>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = aot::udiv(t3, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t5 = t4 ^ t2;
            bool const j18 = aot::nonzero(t5);
            top[-1] = t1;
            top[0] = t2;
            top[1] = t3;
            top += 1;
            if (j18) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_212b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_212b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 832u, 864u, 82>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2137<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2137(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2148<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2148(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1120u, 1152u, 110>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1088u, 1120u, 107>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 864u, 896u, 85>(ctx, gas);
            uint256_t const t3 = aot::mul(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = aot::udiv(t3, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t5 = t4 ^ t2;
            bool const j19 = aot::nonzero(t5);
            top[-2] = t1;
            top[-1] = t2;
            top[0] = t3;
            if (j19) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2174<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2174(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1056u, 1088u, 104>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2180<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2180(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2191<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2191(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x10, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x51, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 1088u, 1120u, 107>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 1088u, 1120u, 107>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1120u, 1152u, 110>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t2 < t1);
            bool const j12 = aot::nonzero(t3);
            top += -3;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x21c4); }
            MONAD_AOT_TAIL return b_21a6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21a6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 1120u, 1152u, 110>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 1088u, 1120u, 107>(ctx, gas);
            uint256_t const t3 = t1 - t2;
            uint256_t const t4 = aot::from_bool(t1 < t3);
            bool const j11 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_21b8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21b8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 544u, 576u, 54>(ctx, gas, s0);
            top += -3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x21d3);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21e1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 800u, 832u, 79>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t3 = t1 - t2;
            uint256_t const t4 = aot::from_bool(t1 < t3);
            bool const j11 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_21f3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21f3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 768u, 800u, 76>(ctx, gas, s0);
            top += -3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x221a);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2212(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x61, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 768u, 800u, 76>(ctx, gas, s0);
            top += -3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x221a);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2245(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 544u, 576u, 54>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t3 = aot::udiv(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = t3 ^ t1;
            bool const j11 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top += 2;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2265<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2265(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x51, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2271<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2271(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x66, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x61, 0x52, 0x66, 0x61, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 512u, 544u, 51>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 512u, 544u, 51>(ctx, gas);
            uint256_t const t3 = aot::from_bool(t2 < uint256_t{0x2386f26fc10000ull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j15 = aot::nonzero(t4);
            top += -2;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2293); }
            MONAD_AOT_TAIL return b_228e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_228e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x22a4);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_22a9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1184u, 1216u, 116>(ctx, gas, uint256_t{0x12ull});
            aot::mstore_c<traits, 1216u, 1248u, 119>(ctx, gas, uint256_t{0x0ull, 0x2079000000000000ull, 0x616c756520666f72ull, 0x556e736166652076ull});
            uint256_t const t1 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t2 = uint256_t{0x4c0ull} + t1;
            uint256_t const t3 = uint256_t{0x0ull} - t1;
            uint256_t const t4 = t3 & uint256_t{0x1full};
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t2, &t5, &t4);
            gas = ctx->gas_remaining;
            aot::mstore_c<traits, 1120u, 1152u, 110>(ctx, gas, uint256_t{0x8c379a0ull});
            aot::mstore_c<traits, 1152u, 1184u, 113>(ctx, gas, uint256_t{0x20ull});
            uint256_t const t6 = aot::mload_c<traits, 1184u, 1216u, 116>(ctx, gas);
            uint256_t const t7 = t6 + uint256_t{0x1full};
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t9 = uint256_t{0x44ull} + t8;
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x47cull}, t9);
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2326(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x60, 0x61, 0x52, 0x7f, 0x61, 0x52, 0x61, 0x50, 0x61, 0x51, 0x80, 0x61, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x61, 0x52, 0x60, 0x61, 0x52, 0x60, 0x19, 0x60, 0x61, 0x51, 0x01, 0x16, 0x60, 0x01, 0x61, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 1152u, 1184u, 113>(ctx, gas, uint256_t{0x10ull});
            aot::mstore_c<traits, 1184u, 1216u, 116>(ctx, gas, uint256_t{0x0ull, 0x0ull, 0x636f6e7665726765ull, 0x446964206e6f7420ull});
            uint256_t const t1 = aot::mload_c<traits, 1152u, 1184u, 113>(ctx, gas);
            uint256_t const t2 = uint256_t{0x4a0ull} + t1;
            uint256_t const t3 = uint256_t{0x0ull} - t1;
            uint256_t const t4 = t3 & uint256_t{0x1full};
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t2, &t5, &t4);
            gas = ctx->gas_remaining;
            aot::mstore_c<traits, 1088u, 1120u, 107>(ctx, gas, uint256_t{0x8c379a0ull});
            aot::mstore_c<traits, 1120u, 1152u, 110>(ctx, gas, uint256_t{0x20ull});
            uint256_t const t6 = aot::mload_c<traits, 1152u, 1184u, 113>(ctx, gas);
            uint256_t const t7 = t6 + uint256_t{0x1full};
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t9 = uint256_t{0x44ull} + t8;
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x45cull}, t9);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_238e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x52, 0x5f, 0x60, 0x52, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x52, 0x5f, 0x60, 0x52, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t1);
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t2 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t3 = aot::shr_c<128>(t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j14 = aot::nonzero(t4);
            if (j14) { MONAD_AOT_TAIL return b_23b2<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_23a4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_23a4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::shr_c<128>(t1);
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t2);
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, uint256_t{0x80ull});
            MONAD_AOT_TAIL return b_23b2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_23b2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<64>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_23d0<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_23be<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_23be(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_23d0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_23d0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<32>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_23ee<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_23dc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_23dc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_23ee<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_23ee(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<16>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_240c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_23fa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_23fa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_240c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_240c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<8>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_242a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2418<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2418(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_242a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_242a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<4>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_2448<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2436<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2436(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_2448<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2448(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<2>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_2466<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2454<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2454(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_2466<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2466(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x1c, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = aot::shr_c<1>(t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_247b<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2472<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2472(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x51, 0x01, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x51, 0x01, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x1ull};
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_247b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_247b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2488); }
            MONAD_AOT_TAIL return b_2483<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2483(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_2493<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2493(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_24a2<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2499<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2499(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x51, 0x01, 0x60, 0x52}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x51, 0x01, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x1ull};
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_24a2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_24a2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 10935)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_24aa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x60, 0x52, 0x78, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x60, 0x52, 0x78, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x4d542c5db2340000ull, 0x5fe645cc4873f9e6ull, 0x725dd1d243aba0e7ull, 0x12ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j10 = aot::nonzero(t3);
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x251e); }
            MONAD_AOT_TAIL return b_24d2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_24d2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x71, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x71, 0x60, 0x51, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xca17a3aba173d3d5ull, 0x484932d2e725a5bbull, 0x154ull, 0x0ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2509); }
            MONAD_AOT_TAIL return b_24ee<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_24ee(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x6e, 0x60, 0x51, 0x02, 0x60, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x6e, 0x60, 0x51, 0x02, 0x60, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull});
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_2525<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2525(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x52, 0x5f, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x52, 0x5f, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t1);
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, uint256_t{0x0ull});
            top[1] = uint256_t{0x253aull};
            top[2] = uint256_t{0x120ull};
            top += 2;
            MONAD_AOT_TAIL return b_238e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_253a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2547<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2547(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x52, 0x61, 0x51, 0x5f, 0x81, 0x12, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x52, 0x61, 0x51, 0x5f, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 256u, 288u, 27>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 256u, 288u, 27>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            bool const j8 = aot::nonzero(t2);
            top[0] = t1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2556<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2556(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x06, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x0a, 0x61, 0x51, 0x61, 0x0a, 0x60, 0x61, 0x51, 0x5f, 0x81, 0x12, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x06, 0x90, 0x50, 0x61, 0x52, 0x61, 0x51, 0x61, 0x0a, 0x61, 0x51, 0x61, 0x0a, 0x60, 0x61, 0x51, 0x5f, 0x81, 0x12, 0x61, 0x57}) + 0;
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
            if (j22) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_257d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_257d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j132) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x269a); }
            MONAD_AOT_TAIL return b_266e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_266e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x71, 0x60, 0x51, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x71, 0x60, 0x51, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0xca17a3aba173d3d5ull, 0x484932d2e725a5bbull, 0x154ull, 0x0ull});
            bool const j5 = aot::nonzero(t2);
            if (j5) { MONAD_AOT_TAIL return b_26aa<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2689<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2689(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x62, 0x61, 0x51, 0x02, 0x61, 0x52, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x62, 0x61, 0x51, 0x02, 0x61, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 320u, 352u, 33>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0xf4240ull});
            aot::mstore_c<traits, 320u, 352u, 33>(ctx, gas, t2);
            MONAD_AOT_TAIL return b_26aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_26aa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 10935)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_26b3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x67, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 0, 9));
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x67, 0x61, 0x51, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 352u, 384u, 36>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 384u, 416u, 39>(ctx, gas);
            uint256_t const t3 = aot::mul(t1, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::udiv(t3, t2);
            uint256_t const t6 = aot::from_bool(t5 == t1);
            uint256_t const t7 = t6 | t4;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j20 = aot::nonzero(t8);
            top[1] = uint256_t{0xde0b6b3a7640000ull};
            top[2] = uint256_t{0xde0b6b3a7640000ull};
            top[3] = t1;
            top[4] = t2;
            top[5] = t3;
            top += 5;
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_26de<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_26de(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            uint256_t const t2 = aot::mload_c<traits, 416u, 448u, 42>(ctx, gas);
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
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_26f7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_26f7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x52, 0x61, 0x51, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x61, 0x52, 0x61, 0x51, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            aot::mstore_c<traits, 448u, 480u, 45>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            bool const j10 = aot::nonzero(t2);
            top += -4;
            if (j10) { MONAD_AOT_TAIL return b_2710<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2708<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2708(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x81, 0x52, 0x50, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x81, 0x52, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, uint256_t{0x0ull});
            top += -1;
            MONAD_AOT_TAIL return b_272a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2710(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x60, 0x52, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 448u, 480u, 45>(ctx, gas);
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t1);
            top[1] = uint256_t{0x2722ull};
            top[2] = uint256_t{0x1e0ull};
            top += 2;
            MONAD_AOT_TAIL return b_24aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2722(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x51, 0x81, 0x52, 0x50}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x51, 0x81, 0x52, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 480u, 512u, 48>(ctx, gas);
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, t1);
            top += -1;
            MONAD_AOT_TAIL return b_272a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_272a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 10935)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_272c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t3 = t1 + t2;
            uint256_t const t4 = aot::from_bool(t3 < t1);
            bool const j12 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top[3] = t3;
            top += 3;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_273d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_273d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x51, 0x80, 0x82, 0x01, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 + t1;
            uint256_t const t3 = aot::from_bool(t2 < s0);
            bool const j13 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = t2;
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_274e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_274e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x52, 0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x60, 0x52, 0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, s0);
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0x29a2241af62c0000ull});
            uint256_t const t3 = aot::udiv(t2, uint256_t{0x29a2241af62c0000ull});
            uint256_t const t4 = t3 ^ t1;
            bool const j17 = aot::nonzero(t4);
            top[-2] = t1;
            top[-1] = t2;
            top += -1;
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2774<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2774(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_277f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_277f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x60, 0x52, 0x60, 0x51, 0x60, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x60, 0x52, 0x60, 0x51, 0x60, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t4 = aot::mul(t3, uint256_t{0x3ull});
            uint256_t const t5 = aot::udiv(t4, uint256_t{0x3ull});
            uint256_t const t6 = t5 ^ t3;
            bool const j22 = aot::nonzero(t6);
            top[-1] = t2;
            top[0] = t3;
            top[1] = t4;
            top += 1;
            if (j22) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_279d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_279d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
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
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_27b2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_27b2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x52, 0x60, 0x51, 0x60, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x52, 0x60, 0x51, 0x60, 0x51, 0x60, 0x81, 0x02, 0x81, 0x60, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t const t3 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t4 = aot::mul(t3, uint256_t{0x3ull});
            uint256_t const t5 = aot::udiv(t4, uint256_t{0x3ull});
            uint256_t const t6 = t5 ^ t3;
            bool const j20 = aot::nonzero(t6);
            top[-3] = t2;
            top[-2] = t3;
            top[-1] = t4;
            top += -1;
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_27ce<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_27ce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x82, 0x02, 0x81, 0x15, 0x83, 0x83, 0x83, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
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
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_27e3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_27e3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x52, 0x60, 0x51, 0x15, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x04, 0x60, 0x52, 0x60, 0x51, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::udiv(s0, s3);
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j11 = aot::nonzero(t3);
            top += -4;
            if (j11) { MONAD_AOT_TAIL return b_284c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_27f3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_27f3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x67, 0x81, 0x02, 0x81, 0x67, 0x82, 0x04, 0x18, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t2 = aot::mul(t1, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t3 = aot::udiv(t2, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t4 = t3 ^ t1;
            bool const j11 = aot::nonzero(t4);
            top[1] = t1;
            top[2] = t2;
            top += 2;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2812<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2812(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x51, 0x67, 0x81, 0x01, 0x81, 0x81, 0x10, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x51, 0x67, 0x81, 0x01, 0x81, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0xde0b6b3a7640000ull};
            uint256_t const t3 = aot::from_bool(t2 < t1);
            bool const j11 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            top[1] = t2;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2829<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2829(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x60, 0x51, 0x80, 0x82, 0x03, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 - t1;
            uint256_t const t3 = aot::from_bool(s0 < t2);
            bool const j11 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = t1;
            top[1] = t2;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2838<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2838(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x15, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x90, 0x50, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j7 = aot::nonzero(t1);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top += -2;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2842<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2842(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x60, 0x52}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x04, 0x90, 0x50, 0x90, 0x50, 0x60, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s1, s0);
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t1);
            top += -2;
            MONAD_AOT_TAIL return b_284c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_284c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x81, 0x52, 0x50, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x81, 0x52, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, t1);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 10935)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2854(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x52, 0x7f, 0x60, 0x51, 0x13, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x52, 0x7f, 0x60, 0x51, 0x13, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, t1);
            uint256_t const t2 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t3 = aot::from_bool(slt(uint256_t{0xb731c958f34d94c1ull, 0xfffffffffffffffdull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t2));
            bool const j10 = aot::nonzero(t3);
            if (j10) { MONAD_AOT_TAIL return b_288c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2884<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2884(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x81, 0x52, 0x50, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x81, 0x52, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, uint256_t{0x0ull});
            top += -1;
            MONAD_AOT_TAIL return b_2aa4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_288c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x68, 0x60, 0x51, 0x13, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x68, 0x60, 0x51, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::from_bool(slt(uint256_t{0x55bf798b4a1bf1e4ull, 0x7ull, 0x0ull, 0x0ull}, t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_28fb<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_28a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_28a0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x52, 0x7f, 0x60, 0x52, 0x60, 0x50, 0x60, 0x51, 0x80, 0x60, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x60, 0x52, 0x60, 0x60, 0x52, 0x60, 0x19, 0x60, 0x60, 0x51, 0x01, 0x16, 0x60, 0x01, 0x60, 0xfd}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x52, 0x7f, 0x60, 0x52, 0x60, 0x50, 0x60, 0x51, 0x80, 0x60, 0x01, 0x60, 0x82, 0x5f, 0x03, 0x16, 0x36, 0x82, 0x37, 0x50, 0x50, 0x63, 0x60, 0x52, 0x60, 0x60, 0x52, 0x60, 0x19, 0x60, 0x60, 0x51, 0x01, 0x16, 0x60, 0x01, 0x60, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, uint256_t{0x10ull});
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, uint256_t{0x0ull, 0x0ull, 0x6f766572666c6f77ull, 0x7761645f65787020ull});
            uint256_t const t1 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t2 = uint256_t{0xa0ull} + t1;
            uint256_t const t3 = uint256_t{0x0ull} - t1;
            uint256_t const t4 = t3 & uint256_t{0x1full};
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t2, &t5, &t4);
            gas = ctx->gas_remaining;
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, uint256_t{0x8c379a0ull});
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, uint256_t{0x20ull});
            uint256_t const t6 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t7 = t6 + uint256_t{0x1full};
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t9 = uint256_t{0x44ull} + t8;
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x5cull}, t9);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_28fb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x65, 0x60, 0x51, 0x60, 0x1b, 0x05, 0x60, 0x52, 0x6b, 0x6b, 0x60, 0x51, 0x60, 0x1b, 0x05, 0x01, 0x60, 0x1d, 0x60, 0x52, 0x6b, 0x60, 0x51, 0x02, 0x60, 0x51, 0x03, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x6c, 0x60, 0x51, 0x01, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x79, 0x60, 0x51, 0x6e, 0x60, 0x51, 0x6d, 0x60, 0x51, 0x60, 0x51, 0x01, 0x03, 0x02, 0x60, 0x1d, 0x01, 0x02, 0x01, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x6c, 0x60, 0x51, 0x03, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x03, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x6e, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x03, 0x60, 0x52, 0x6e, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x60, 0x51, 0x60, 0x51, 0x05, 0x61, 0x52, 0x74, 0x61, 0x51, 0x02, 0x60, 0x51, 0x60, 0x03, 0x5f, 0x81, 0x12, 0x61, 0x57}, 0, 7));
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x65, 0x60, 0x51, 0x60, 0x1b, 0x05, 0x60, 0x52, 0x6b, 0x6b, 0x60, 0x51, 0x60, 0x1b, 0x05, 0x01, 0x60, 0x1d, 0x60, 0x52, 0x6b, 0x60, 0x51, 0x02, 0x60, 0x51, 0x03, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x6c, 0x60, 0x51, 0x01, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x79, 0x60, 0x51, 0x6e, 0x60, 0x51, 0x6d, 0x60, 0x51, 0x60, 0x51, 0x01, 0x03, 0x02, 0x60, 0x1d, 0x01, 0x02, 0x01, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x6c, 0x60, 0x51, 0x03, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x03, 0x60, 0x52, 0x6d, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x6e, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x03, 0x60, 0x52, 0x6e, 0x60, 0x51, 0x60, 0x51, 0x02, 0x60, 0x1d, 0x01, 0x60, 0x52, 0x60, 0x51, 0x60, 0x51, 0x05, 0x61, 0x52, 0x74, 0x61, 0x51, 0x02, 0x60, 0x51, 0x60, 0x03, 0x5f, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::shl_c<78>(t1);
            uint256_t const k6_1 = uint256_t{0x3782dace9d9ull};
            uint256_t r6;
            runtime::sdiv(&r6, &t2, &k6_1);
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, r6);
            uint256_t const t3 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t4 = aot::shl_c<96>(t3);
            uint256_t const k15_1 = uint256_t{0xd1cf79abc9e3b398ull, 0xb17217f7ull, 0x0ull, 0x0ull};
            uint256_t r15;
            runtime::sdiv(&r15, &t4, &k15_1);
            uint256_t const t5 = r15 + uint256_t{0x0ull, 0x80000000ull, 0x0ull, 0x0ull};
            uint256_t const t6 = sar(uint256_t{0x60ull}, t5);
            aot::mstore_c<traits, 128u, 160u, 15>(ctx, gas, t6);
            uint256_t const t7 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t8 = aot::mul(t7, uint256_t{0xd1cf79abc9e3b398ull, 0xb17217f7ull, 0x0ull, 0x0ull});
            uint256_t const t9 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t10 = t9 - t8;
            aot::mstore_c<traits, 96u, 128u, 12>(ctx, gas, t10);
            uint256_t const t11 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t12 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t13 = t12 + uint256_t{0x37d0007b713f7650ull, 0x10fe68e7fdull, 0x0ull, 0x0ull};
            uint256_t const t14 = aot::mul(t13, t11);
            uint256_t const t15 = sar(uint256_t{0x60ull}, t14);
            uint256_t const t16 = t15 + uint256_t{0xd19bf614176fe9eaull, 0x2d16720577bull, 0x0ull, 0x0ull};
            aot::mstore_c<traits, 160u, 192u, 18>(ctx, gas, t16);
            uint256_t const t17 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t18 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t19 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t20 = aot::mload_c<traits, 160u, 192u, 18>(ctx, gas);
            uint256_t const t21 = t20 + t19;
            uint256_t const t22 = t21 - uint256_t{0x96949216d2255a6cull, 0x4a4fd9f2a8bull, 0x0ull, 0x0ull};
            uint256_t const t23 = aot::mul(t22, t18);
            uint256_t const t24 = sar(uint256_t{0x60ull}, t23);
            uint256_t const t25 = t24 + uint256_t{0x9d25fcb740196450ull, 0x587f503bb6ea2ull, 0x0ull, 0x0ull};
            uint256_t const t26 = aot::mul(t25, t17);
            uint256_t const t27 = t26 + uint256_t{0x0ull, 0x3b2ca45c00000000ull, 0xebba824c98fb31b8ull, 0xd835ull};
            aot::mstore_c<traits, 192u, 224u, 21>(ctx, gas, t27);
            uint256_t const t28 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t29 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t30 = t29 - uint256_t{0xb2d9cbaf0fd5aafcull, 0x240c330e9full, 0x0ull, 0x0ull};
            uint256_t const t31 = aot::mul(t30, t28);
            uint256_t const t32 = sar(uint256_t{0x60ull}, t31);
            uint256_t const t33 = t32 + uint256_t{0xc85f6e2461837cd9ull, 0x277594991cfull, 0x0ull, 0x0ull};
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t33);
            uint256_t const t34 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t35 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t36 = aot::mul(t35, t34);
            uint256_t const t37 = sar(uint256_t{0x60ull}, t36);
            uint256_t const t38 = t37 - uint256_t{0x6a5061b25ef1c9c4ull, 0x1a521255e34full, 0x0ull, 0x0ull};
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t38);
            uint256_t const t39 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t40 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t41 = aot::mul(t40, t39);
            uint256_t const t42 = sar(uint256_t{0x60ull}, t41);
            uint256_t const t43 = t42 + uint256_t{0xcf962f1a1d3db4a5ull, 0xb1bbb201f443ull, 0x0ull, 0x0ull};
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t43);
            uint256_t const t44 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t45 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t46 = aot::mul(t45, t44);
            uint256_t const t47 = sar(uint256_t{0x60ull}, t46);
            uint256_t const t48 = t47 - uint256_t{0x51a9331fed693f15ull, 0x2c72388d9f74full, 0x0ull, 0x0ull};
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t48);
            uint256_t const t49 = aot::mload_c<traits, 96u, 128u, 12>(ctx, gas);
            uint256_t const t50 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t51 = aot::mul(t50, t49);
            uint256_t const t52 = sar(uint256_t{0x60ull}, t51);
            uint256_t const t53 = t52 + uint256_t{0x47a8a8cb2a527d57ull, 0x5180bb14799abull, 0x0ull, 0x0ull};
            aot::mstore_c<traits, 224u, 256u, 24>(ctx, gas, t53);
            uint256_t const t54 = aot::mload_c<traits, 224u, 256u, 24>(ctx, gas);
            uint256_t const t55 = aot::mload_c<traits, 192u, 224u, 21>(ctx, gas);
            uint256_t r125;
            runtime::sdiv(&r125, &t55, &t54);
            aot::mstore_c<traits, 256u, 288u, 27>(ctx, gas, r125);
            uint256_t const t56 = aot::mload_c<traits, 256u, 288u, 27>(ctx, gas);
            uint256_t const t57 = aot::mul(t56, uint256_t{0xee70ef65f9978af3ull, 0x63c32e5c2f6dc192ull, 0x29d9dc385ull, 0x0ull});
            uint256_t const t58 = aot::mload_c<traits, 128u, 160u, 15>(ctx, gas);
            uint256_t const t59 = uint256_t{0xc3ull} - t58;
            uint256_t const t60 = aot::from_bool(slt(t59, uint256_t{0x0ull}));
            bool const j140 = aot::nonzero(t60);
            top[1] = t57;
            top[2] = t59;
            top += 2;
            if (j140) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2aa6); }
            MONAD_AOT_TAIL return b_2aa0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2aa0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x1c, 0x81, 0x52, 0x50}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x1c, 0x81, 0x52, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr(s0, s1);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, t1);
            top += -3;
            MONAD_AOT_TAIL return b_2aa4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2aa4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 10935)) {
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

    template void c_4031de700c2e5e41::run<EvmTraits<MONAD_ETH_OSAKA>>(
        void *, Context *, interpreter::Intercode const *, uint256_t *, void *);
}
