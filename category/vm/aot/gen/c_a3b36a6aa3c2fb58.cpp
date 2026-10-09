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

// Written by aotgen.py from the code whose keccak is a3b36a6aa3c2fb588b92336d88b0735b40dea0282c110d2034edf688ca661b5b: not to be edited.

#include <category/vm/aot/ops.hpp>
#include <category/vm/interpreter/execute.hpp>
#include <category/vm/interpreter/intercode.hpp>

#define MONAD_AOT_TAIL __attribute__((musttail))

namespace monad::vm::aot
{
    using runtime::Context;
    using runtime::StatusCode;

    // 7746 bytes, keccak a3b36a6aa3c2fb588b92336d88b0735b40dea0282c110d2034edf688ca661b5b
    namespace c_a3b36a6aa3c2fb58
    {
        template <Traits traits>
        using Block = void (*)(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        [[gnu::noinline]] void b_0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_15(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_36(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_41(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_57(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_62(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_78(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_83(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_8e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_99(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_af(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_cd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_109(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_10e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_123(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_130(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_132(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_13f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_178(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_198(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1af(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ca(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_201(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_205(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_222(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_226(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_235(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_244(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_24c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_25a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_266(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_279(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_286(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_291(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_29f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2bb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2c3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2de(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2f8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_303(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_318(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_325(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_336(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_347(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_348(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_355(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_366(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_374(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_375(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_384(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_390(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_39c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3aa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3b8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3c6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3d3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3e1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3e4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_408(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_42b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_433(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_43a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_46b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_47a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_487(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_48e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4a0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_4ad(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4c0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_4cd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_4d8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_4e1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4f3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_500(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_516(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_52a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_530(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_53c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_540(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_549(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_556(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_593(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_5a3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6e0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6eb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_70f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_71b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_73d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_76c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_7af(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_7c0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_804(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_847(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_852(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_881(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_88c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_8ad(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_8b8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_8ee(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_91b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_93f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_95c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_97e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_98f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9a0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9ae(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9bf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9de(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a00(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a32(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a4e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a5b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a6c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a79(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a8b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a98(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_aad(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_aba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ac2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_acb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_adf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_af3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b08(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b19(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b24(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b37(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b46(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b57(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b8a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_bb0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_bbc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_be0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_be9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_bea(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_bf5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c06(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c13(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c1e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c2c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c44(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c49(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c51(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c58(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c69(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c7a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c86(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c94(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_caa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_cbb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_cc6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_cd3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ce3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d03(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d23(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d4f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d57(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d86(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d93(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_dad(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_db9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_dd2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_df7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e0d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e16(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_e2f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_e3d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_e48(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e5f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_e65(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_e8c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ec3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ec9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ecc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ee0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ee8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_eff(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f0a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f12(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f1d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f43(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f4f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f81(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f91(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fa0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fb0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fb6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fbd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fcb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fd7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fe0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1021(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_102a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_104e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_105a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1064(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1072(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1080(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1086(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10a7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10c8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10e0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10ec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_114a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1154(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_115a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1164(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1171(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_117f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1195(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1197(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_119f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_11a5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11b6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11c2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_11ce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_11d9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_11e9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_120d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_121b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_122b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1277(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1286(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12b3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_12df(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12f6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12fc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1333(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1338(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_13a5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1416(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_14b1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14c4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14d3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_14f7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14ff(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1529(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1540(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_154c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1555(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1571(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1582(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1590(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_15a3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_15b5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_163b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1667(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_16c6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1786(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1790(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_179d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_17ae(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_17b2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_17ba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_17be(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_17cd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_17e1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_17eb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_17f5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1805(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_180d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1812(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1839(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1844(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1870(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1878(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_18ae(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_18c0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_18d2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_18e0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1919(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1962(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1978(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_19c5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_19db(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_19de(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_19e8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_19f7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a06(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a0e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a1d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a30(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a92(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1aa0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1aad(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ab4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ad5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1b3f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1b45(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ba7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c07(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c3f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c4d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c92(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1cbb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1cdb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ce5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1cf3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1cfd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d03(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d0f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d16(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d33(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d44(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d51(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d55(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d5c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d64(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d6e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d7b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d8c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d96(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1da0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1da8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1dad(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1dc3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dc9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dd1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1dd8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1de7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1df0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1df5(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        void bad(Context *const ctx, uint256_t const *, uint256_t *, int64_t)
        {
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        inline constexpr Block<traits> jump_table[7746] = {
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &b_1a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &b_cd<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_109<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_10e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_123<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_130<traits>, &bad<traits>,
            &b_132<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_13f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_178<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_198<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1ce<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_205<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_226<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_235<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_24c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_266<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_291<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_29f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2bb<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2de<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2f8<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_303<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_318<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_348<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_375<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_390<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_39c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_3aa<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3c6<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3e1<traits>, &bad<traits>, &bad<traits>,
            &b_3e4<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_408<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_42b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_43a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_46b<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_47a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_48e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_4ad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_4cd<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_4d8<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_4e1<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_500<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_52a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_530<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_53c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_540<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_593<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_5a3<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_7af<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_a4e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_a79<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_a98<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_aba<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_ac2<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_acb<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_af3<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_be0<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_bea<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_c1e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_c2c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_c49<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_c58<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_c86<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_c94<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_cc6<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_cd3<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_d03<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_d23<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_d4f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_d86<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_d93<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_db9<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_dd2<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_e2f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_e3d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_e48<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_e65<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_e8c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_ecc<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_ee0<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_ee8<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_eff<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_f0a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_f12<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_f1d<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_f43<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_f81<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_f91<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_fa0<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_fb0<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_fb6<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_fbd<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_fcb<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_fd7<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_fe0<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1021<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_104e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1064<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1072<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1080<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1086<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_114a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_115a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1164<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1171<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_117f<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1197<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_11a5<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_11ce<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_11d9<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_11e9<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_121b<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_122b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_12df<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1333<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1338<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_14b1<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_14f7<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1529<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1540<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_154c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1555<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1571<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1582<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1590<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1786<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1790<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_179d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_17ae<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_17b2<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_17be<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_17cd<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_17e1<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_17f5<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1805<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1812<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1839<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1844<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1870<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_18ae<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_18c0<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_18d2<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_18e0<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &b_1962<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &b_19c5<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_19db<traits>, &bad<traits>, &bad<traits>, &b_19de<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_19f7<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1a06<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1a0e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1a1d<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1a30<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1a92<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1aa0<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1aad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1ab4<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1ad5<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1b3f<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1b45<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1cbb<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1ce5<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1cf3<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1cfd<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1d03<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1d0f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1d33<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1d51<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1d55<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1d5c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1d64<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1d6e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1d7b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1d8c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1d96<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1da0<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1dad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1dc3<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1dd8<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1de7<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1df0<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
        };

        template <Traits traits>
        [[gnu::noinline]] void b_0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j8) { MONAD_AOT_TAIL return b_1a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xe);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_15(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x35, 0x60, 0x1c, 0x80, 0x63, 0x14, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x35, 0x60, 0x1c, 0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x0ull});
            uint256_t const t2 = aot::shr_c<224>(t1);
            uint256_t const t3 = aot::from_bool(uint256_t{0xa2b8f36ull} == t2);
            bool const j9 = aot::nonzero(t3);
            top[1] = t2;
            top += 1;
            if (j9) { MONAD_AOT_TAIL return b_109<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x25692962ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x104); }
            MONAD_AOT_TAIL return b_36<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_36(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x3806a3cfull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xff); }
            MONAD_AOT_TAIL return b_41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_41(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x51cff8d9ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xfa); }
            MONAD_AOT_TAIL return b_4c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x54d1f13dull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xf5); }
            MONAD_AOT_TAIL return b_57<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_57(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x715018a6ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xf0); }
            MONAD_AOT_TAIL return b_62<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_62(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x8bd9105dull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xeb); }
            MONAD_AOT_TAIL return b_6d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x8da5cb5bull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xe6); }
            MONAD_AOT_TAIL return b_78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_78(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xcf641c61ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xe1); }
            MONAD_AOT_TAIL return b_83<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_83(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xf04e283eull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xdc); }
            MONAD_AOT_TAIL return b_8e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_8e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xf2fde38bull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xd7); }
            MONAD_AOT_TAIL return b_99<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_99(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xf80f00fbull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xd2); }
            MONAD_AOT_TAIL return b_a4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xf9e4bab4ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_cd<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_af<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_af(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xfb68c293ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc8); }
            MONAD_AOT_TAIL return b_ba<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x63, 0x03, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x63, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0xfee81cf4ull} - s0;
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xe); }
            MONAD_AOT_TAIL return b_c4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xbaa);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_cd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_a4e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_109(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_47a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_10e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x16, 0x03, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x16, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = t1 - s0;
            bool const j10 = aot::nonzero(t2);
            top += -1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_11e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_123(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x130ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_10e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_130(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_132(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x130ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_10e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_13f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x130ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_10e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_178(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x82, 0x11, 0x17, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x82, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x60ull};
            uint256_t const t2 = aot::from_bool(t1 < s0);
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            uint256_t const t4 = t3 | t2;
            bool const j16 = aot::nonzero(t4);
            top[0] = t1;
            if (j16) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x193); }
            MONAD_AOT_TAIL return b_18f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x52, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_198(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x82, 0x11, 0x17, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x82, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x40ull};
            uint256_t const t2 = aot::from_bool(t1 < s0);
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            uint256_t const t4 = t3 | t2;
            bool const j16 = aot::nonzero(t4);
            top[0] = t1;
            if (j16) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x193); }
            MONAD_AOT_TAIL return b_1af<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1af(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x52, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ca(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x52, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x82, 0x11, 0x17, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x82, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x80ull};
            uint256_t const t2 = aot::from_bool(t1 < s0);
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            uint256_t const t4 = t3 | t2;
            bool const j16 = aot::nonzero(t4);
            top[0] = t1;
            if (j16) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x193); }
            MONAD_AOT_TAIL return b_1e5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x52, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_201(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x52, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_205(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x60, 0x80, 0x19, 0x91, 0x01, 0x16, 0x81, 0x01, 0x90, 0x81, 0x10, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x82, 0x11, 0x17, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x60, 0x80, 0x19, 0x91, 0x01, 0x16, 0x81, 0x01, 0x90, 0x81, 0x10, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x82, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x1full};
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s0 = top[0];
            uint256_t const t3 = s0 + t2;
            uint256_t const t4 = aot::from_bool(t3 < s0);
            uint256_t const t5 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t3);
            uint256_t const t6 = t5 | t4;
            bool const j22 = aot::nonzero(t6);
            top[-1] = t3;
            top += -1;
            if (j22) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x193); }
            MONAD_AOT_TAIL return b_222<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_222(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x52, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_226(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x60, 0x83, 0x61, 0x56}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x60, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x130ull};
            top[3] = uint256_t{0x40ull};
            top[4] = t1;
            top += 4;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_235(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xffffffffffffffffull} < s0);
            bool const j9 = aot::nonzero(t1);
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x193); }
            MONAD_AOT_TAIL return b_244<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_244(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1b, 0x60, 0x01, 0x90, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1b, 0x60, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const t2 = uint256_t{0x20ull} + t1;
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top[-1] = t2;
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_24c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x90, 0x91, 0x60, 0x81, 0x84, 0x03, 0x12, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x90, 0x91, 0x60, 0x81, 0x84, 0x03, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 - s0;
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x60ull}));
            bool const j10 = aot::nonzero(t2);
            uint256_t const m1 = s1;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m1;
            top[-1] = m2;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_25a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_25a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x266ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_178<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_266(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x93, 0x81, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x93, 0x81, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j13 = aot::nonzero(t2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = m1;
            top[1] = m3;
            top[2] = t1;
            top += 2;
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_279<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_279(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x01, 0x81, 0x60, 0x82, 0x01, 0x12, 0x15, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x01, 0x81, 0x60, 0x82, 0x01, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s2 + s0;
            uint256_t const t2 = t1 + uint256_t{0x1full};
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::from_bool(slt(t2, s1));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j9 = aot::nonzero(t4);
            top[0] = t1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_286<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_286(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x35, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x35, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x291ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_235<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_291(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x61, 0x60, 0x51, 0x94, 0x85, 0x61, 0x56}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x61, 0x60, 0x51, 0x94, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-3] = t1;
            top[0] = m3;
            top[1] = uint256_t{0x29full};
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_29f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x84, 0x52, 0x60, 0x80, 0x85, 0x01, 0x93, 0x60, 0x1b, 0x83, 0x01, 0x01, 0x91, 0x81, 0x83, 0x11, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x84, 0x52, 0x60, 0x80, 0x85, 0x01, 0x93, 0x60, 0x1b, 0x83, 0x01, 0x01, 0x91, 0x81, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s3, s2);
            uint256_t const t1 = s3 + uint256_t{0x20ull};
            uint256_t const t2 = aot::shl_c<6>(s2);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = s1 + t2;
            uint256_t const t4 = t3 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            uint256_t const t5 = aot::from_bool(s0 < t4);
            bool const j19 = aot::nonzero(t5);
            uint256_t const m1 = s1;
            top[-2] = t1;
            top[-1] = t4;
            top[1] = m1;
            top += 1;
            if (j19) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_2b7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x01, 0x92}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x01, 0x92}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x20ull} + s0;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = t1;
            top[0] = m3;
            MONAD_AOT_TAIL return b_2bb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2bb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x84, 0x10, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x84, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(s3 < s2);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_2de<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2c3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2c3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x60, 0x91, 0x82, 0x91, 0x84, 0x52, 0x60, 0x81, 0x01, 0x35, 0x60, 0x85, 0x01, 0x52, 0x01, 0x35, 0x91, 0x01, 0x52, 0x56}, 8, 0));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x60, 0x91, 0x82, 0x91, 0x84, 0x52, 0x60, 0x81, 0x01, 0x35, 0x60, 0x85, 0x01, 0x52, 0x01, 0x35, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, s6, s4);
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = s5 + uint256_t{0x20ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const t3 = s6 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = s5 + uint256_t{0x40ull};
            uint256_t const t5 = aot::calldataload(ctx, t4);
            uint256_t const t6 = s6 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t6, t5);
            uint256_t const &s7 = top[-7];
            uint64_t const jt = aot::jump_offset(s7);
            top += -8;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2de(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x84, 0x83, 0x03, 0x12, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x84, 0x83, 0x03, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s1 - s3;
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x40ull}));
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_2e9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x91, 0x82, 0x51, 0x61, 0x81, 0x61, 0x56}, 1, 6));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x91, 0x82, 0x51, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x40ull};
            top[1] = uint256_t{0x20ull};
            top[2] = m0;
            top[3] = t1;
            top[4] = uint256_t{0x2f8ull};
            top[5] = t1;
            top += 5;
            MONAD_AOT_TAIL return b_198<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2f8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x86, 0x35, 0x61, 0x81, 0x61, 0x56}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x86, 0x35, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::calldataload(ctx, s6);
            top[1] = t1;
            top[2] = uint256_t{0x303ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_10e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_303(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x52, 0x82, 0x87, 0x01, 0x35, 0x83, 0x82, 0x01, 0x52, 0x81, 0x52, 0x01, 0x93, 0x01, 0x92, 0x61, 0x56}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x52, 0x82, 0x87, 0x01, 0x35, 0x83, 0x82, 0x01, 0x52, 0x81, 0x52, 0x01, 0x93, 0x01, 0x92, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s1, s0);
            uint256_t const &s7 = top[-7];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s7 + s3;
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const t3 = s1 + s3;
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, s1);
            uint256_t const t4 = s2 + s3;
            uint256_t const &s4 = top[-4];
            uint256_t const t5 = s7 + s4;
            top[-7] = t5;
            top[-4] = t4;
            top += -4;
            MONAD_AOT_TAIL return b_2bb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_318(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_325<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_325(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x35, 0x91, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x83, 0x11, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x35, 0x91, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::calldataload(ctx, s2);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j11 = aot::nonzero(t2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[1] = m1;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_336<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_336(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0x85, 0x01, 0x94, 0x84, 0x60, 0x1b, 0x01, 0x01, 0x11, 0x61, 0x57}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0x85, 0x01, 0x94, 0x84, 0x60, 0x1b, 0x01, 0x01, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x20ull};
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = aot::shl_c<5>(s2);
            uint256_t const t3 = t2 + s3;
            uint256_t const t4 = t3 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            uint256_t const t5 = aot::from_bool(s0 < t4);
            bool const j12 = aot::nonzero(t5);
            top[-3] = t1;
            top += -1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_347<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_347(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_348(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_355<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_355(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x35, 0x91, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x83, 0x11, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x35, 0x91, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::calldataload(ctx, s2);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j11 = aot::nonzero(t2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[1] = m1;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_366<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_366(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_374<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_374(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_375(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xffffffffffffffffull} < s0);
            bool const j9 = aot::nonzero(t1);
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x193); }
            MONAD_AOT_TAIL return b_384<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_384(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x01, 0x60, 0x19, 0x16, 0x60, 0x01, 0x90, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x01, 0x60, 0x19, 0x16, 0x60, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x1full} + s0;
            uint256_t const t2 = uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} & t1;
            uint256_t const t3 = uint256_t{0x20ull} + t2;
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top[-1] = t3;
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_390(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x91, 0x92, 0x61, 0x82, 0x61, 0x56}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x91, 0x92, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-3] = m2;
            top[-2] = m3;
            top[1] = uint256_t{0x39cull};
            top[2] = m1;
            top += 2;
            MONAD_AOT_TAIL return b_375<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_39c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x61, 0x60, 0x51, 0x93, 0x84, 0x61, 0x56}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x61, 0x60, 0x51, 0x93, 0x84, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = t1;
            top[0] = m2;
            top[1] = uint256_t{0x3aaull};
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3aa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x94, 0x81, 0x84, 0x52, 0x81, 0x83, 0x01, 0x11, 0x61, 0x57}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x94, 0x81, 0x84, 0x52, 0x81, 0x83, 0x01, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s2, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + s0;
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = aot::from_bool(s4 < t1);
            bool const j11 = aot::nonzero(t2);
            uint256_t const m2 = s2;
            top[-4] = m2;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_3b8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3b8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x81, 0x60, 0x93, 0x84, 0x5f, 0x96, 0x01, 0x37, 0x01, 0x01, 0x52, 0x56}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x81, 0x60, 0x93, 0x84, 0x5f, 0x96, 0x01, 0x37, 0x01, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0x20ull};
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t1, &s1, &s0);
            gas = ctx->gas_remaining;
            uint256_t const t2 = s2 + s0;
            uint256_t const t3 = t2 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0x0ull});
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top += -4;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3c6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x80, 0x60, 0x83, 0x01, 0x12, 0x15, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x80, 0x60, 0x83, 0x01, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x1full};
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::from_bool(slt(t1, s1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j9 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            uint256_t const m1 = s1;
            top[-1] = m0;
            top[0] = m1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_3d3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3d3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x61, 0x93, 0x35, 0x91, 0x01, 0x61, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x61, 0x93, 0x35, 0x91, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::calldataload(ctx, s1);
            uint256_t const t2 = s1 + uint256_t{0x20ull};
            top[-1] = uint256_t{0x3e1ull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_390<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3e1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3e4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x51, 0x80, 0x83, 0x52, 0x60, 0x92, 0x91, 0x81, 0x90, 0x84, 0x01, 0x84, 0x84, 0x01, 0x5e, 0x5f, 0x82, 0x82, 0x01, 0x84, 0x01, 0x52, 0x60, 0x01, 0x60, 0x19, 0x16, 0x01, 0x01, 0x90, 0x56}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x51, 0x80, 0x83, 0x52, 0x60, 0x92, 0x91, 0x81, 0x90, 0x84, 0x01, 0x84, 0x84, 0x01, 0x5e, 0x5f, 0x82, 0x82, 0x01, 0x84, 0x01, 0x52, 0x60, 0x01, 0x60, 0x19, 0x16, 0x01, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, t1);
            uint256_t const t2 = uint256_t{0x20ull} + s0;
            uint256_t const t3 = s1 + uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::mcopy<traits>(ctx, &t3, &t2, &t1);
            gas = ctx->gas_remaining;
            uint256_t const t4 = t1 + s1;
            uint256_t const t5 = uint256_t{0x20ull} + t4;
            aot::mstore<traits>(ctx, gas, t5, uint256_t{0x0ull});
            uint256_t const t6 = uint256_t{0x1full} + t1;
            uint256_t const t7 = uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} & t6;
            uint256_t const t8 = t7 + s1;
            uint256_t const t9 = t8 + uint256_t{0x20ull};
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t9;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_408(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x01, 0x60, 0x82, 0x52, 0x82, 0x51, 0x80, 0x91, 0x52, 0x60, 0x82, 0x01, 0x91, 0x60, 0x60, 0x83, 0x60, 0x1b, 0x83, 0x01, 0x01, 0x94, 0x01, 0x92, 0x5f, 0x91}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x01, 0x60, 0x82, 0x52, 0x82, 0x51, 0x80, 0x91, 0x52, 0x60, 0x82, 0x01, 0x91, 0x60, 0x60, 0x83, 0x60, 0x1b, 0x83, 0x01, 0x01, 0x94, 0x01, 0x92, 0x5f, 0x91}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, s0, uint256_t{0x20ull});
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::mload<traits>(ctx, gas, s1);
            aot::mstore<traits>(ctx, gas, t1, t2);
            uint256_t const t3 = s0 + uint256_t{0x40ull};
            uint256_t const t4 = aot::shl_c<5>(t2);
            uint256_t const t5 = s0 + t4;
            uint256_t const t6 = t5 + uint256_t{0x40ull};
            uint256_t const t7 = s1 + uint256_t{0x20ull};
            uint256_t const m0 = s0;
            top[-1] = t6;
            top[0] = t7;
            top[1] = t2;
            top[2] = uint256_t{0x0ull};
            top[3] = t3;
            top[4] = m0;
            top += 4;
            MONAD_AOT_TAIL return b_42b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_42b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j5) { MONAD_AOT_TAIL return b_43a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_433<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_433(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x90, 0x56}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint64_t const jt = aot::jump_offset(s6);
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-6] = m5;
            top += -6;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_43a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x91, 0x92, 0x93, 0x94, 0x60, 0x80, 0x61, 0x60, 0x93, 0x60, 0x19, 0x86, 0x82, 0x03, 0x01, 0x87, 0x52, 0x60, 0x83, 0x8b, 0x51, 0x80, 0x51, 0x15, 0x15, 0x84, 0x52, 0x01, 0x51, 0x91, 0x81, 0x85, 0x82, 0x01, 0x52, 0x01, 0x90, 0x61, 0x56}, 6, 9));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x91, 0x92, 0x93, 0x94, 0x60, 0x80, 0x61, 0x60, 0x93, 0x60, 0x19, 0x86, 0x82, 0x03, 0x01, 0x87, 0x52, 0x60, 0x83, 0x8b, 0x51, 0x80, 0x51, 0x15, 0x15, 0x84, 0x52, 0x01, 0x51, 0x91, 0x81, 0x85, 0x82, 0x01, 0x52, 0x01, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s5 - s0;
            uint256_t const t2 = t1 + uint256_t{0xffffffffffffffc0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, t2);
            uint256_t const &s4 = top[-4];
            uint256_t const t3 = aot::mload<traits>(ctx, gas, s4);
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            aot::mstore<traits>(ctx, gas, s5, t6);
            uint256_t const t7 = t3 + uint256_t{0x20ull};
            uint256_t const t8 = aot::mload<traits>(ctx, gas, t7);
            uint256_t const t9 = s5 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t9, uint256_t{0x40ull});
            uint256_t const t10 = s5 + uint256_t{0x40ull};
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const m1 = s1;
            uint256_t const m0 = s0;
            top[-5] = m4;
            top[-4] = m3;
            top[-3] = m2;
            top[-2] = m1;
            top[-1] = m0;
            top[0] = uint256_t{0x1ull};
            top[1] = uint256_t{0x20ull};
            top[2] = uint256_t{0x20ull};
            top[3] = uint256_t{0x46bull};
            top[4] = t10;
            top[5] = t8;
            top += 5;
            MONAD_AOT_TAIL return b_3e4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_46b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x97, 0x01, 0x93, 0x01, 0x93, 0x01, 0x91, 0x93, 0x92, 0x90, 0x61, 0x56}, 9, 0));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x97, 0x01, 0x93, 0x01, 0x93, 0x01, 0x91, 0x93, 0x92, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s8 + s1;
            uint256_t const &s5 = top[-5];
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s5 + s2;
            uint256_t const &s6 = top[-6];
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = s6 + s3;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-8] = m0;
            top[-7] = t1;
            top[-6] = m7;
            top[-5] = t3;
            top[-4] = t2;
            top[-3] = m4;
            top += -3;
            MONAD_AOT_TAIL return b_42b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_47a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0xe0ull}));
            bool const j8 = aot::nonzero(t3);
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_487<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_487(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x48eull};
            top += 1;
            MONAD_AOT_TAIL return b_123<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_48e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j11 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_4a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4a0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0x4adull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_24c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_4ad(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j12 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = m0;
            top[0] = m1;
            top[1] = t1;
            top += 1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_4c0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4c0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0x4cdull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_318<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_4cd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x92, 0x91, 0x92, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x92, 0x91, 0x92, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m1;
            top[-1] = m2;
            top[1] = uint256_t{0x4d8ull};
            top += 1;
            MONAD_AOT_TAIL return b_132<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_4d8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x61, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = m0;
            top[0] = m1;
            top[1] = uint256_t{0x4e1ull};
            top += 1;
            MONAD_AOT_TAIL return b_13f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_4e1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j11 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_4f3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4f3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0x500ull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_348<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_500(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x93, 0x90, 0x92, 0x60, 0x35, 0x96, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x88, 0x11, 0x61, 0x57}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x93, 0x90, 0x92, 0x60, 0x35, 0x96, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x88, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xc4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j15 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-6] = t1;
            top[-4] = m0;
            top[-3] = m1;
            top[-1] = m4;
            top[0] = m3;
            top[1] = m6;
            top += 1;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_516<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_516(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x98, 0x61, 0x61, 0x99, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 9, 5));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x98, 0x61, 0x61, 0x99, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s7 = top[-7];
            uint256_t const t2 = uint256_t{0x4ull} + s7;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-8] = uint256_t{0x53cull};
            top[-7] = uint256_t{0x530ull};
            top[1] = m8;
            top[2] = uint256_t{0x52aull};
            top[3] = t1;
            top[4] = t2;
            top += 4;
            MONAD_AOT_TAIL return b_3c6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_52a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x97, 0x61, 0x56}, 9, 1));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x97, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-8] = m0;
            top[0] = m8;
            MONAD_AOT_TAIL return b_e48<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_530(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x91, 0x82, 0x91, 0x82, 0x61, 0x56}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x91, 0x82, 0x91, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = t1;
            top[0] = t1;
            top[1] = m1;
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_408<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_53c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
        [[gnu::noinline]] void b_540(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x91, 0x03, 0x12, 0x61, 0x57}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x91, 0x03, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 - s0;
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            bool const j6 = aot::nonzero(t2);
            top += -2;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_549<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_549(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_556(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x63, 0x60, 0x52, 0x33, 0x5f, 0x52, 0x62, 0x42, 0x01, 0x60, 0x60, 0x20, 0x55, 0x33, 0x7f, 0x5f, 0x80, 0xa2, 0x00}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x63, 0x60, 0x52, 0x33, 0x5f, 0x52, 0x62, 0x42, 0x01, 0x60, 0x60, 0x20, 0x55, 0x33, 0x7f, 0x5f, 0x80, 0xa2, 0x00}) + 6;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 12u, 64u, 6>(ctx, gas, uint256_t{0x389a75e1ull});
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const t3 = t2 + uint256_t{0x2a300ull};
            uint256_t const t4 = aot::sha3_n<traits, 32>(ctx, gas, uint256_t{0xcull});
            aot::sstore<traits>(ctx, gas, t4, t3, (aot::gas_of<traits>({0x33, 0x7f, 0x5f, 0x80, 0xa2, 0x00}) + 0));
            uint256_t const t5 = runtime::uint256_from_address(ctx->env.sender);
            aot::log2<traits>(ctx, gas, uint256_t{0x0ull}, uint256_t{0x0ull}, uint256_t{0x5d6cd8f1f9ac7e1dull, 0x3b4b0ff8cde35ee3ull, 0x527a7176a1babf96ull, 0xdbf36a107da19e49ull}, t5);
            gas = ctx->gas_remaining;
            aot::stop(ctx, gas);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_593(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x61, 0x83, 0x61, 0x56}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x61, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x5a3ull};
            top[3] = uint256_t{0x120ull};
            top[4] = t1;
            top += 4;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_5a3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x61, 0x83, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x01, 0x52, 0x56}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x61, 0x83, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x7f, 0x60, 0x82, 0x01, 0x52, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0xfbull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x616c6c3356616c75ull, 0x69746e6573732943ull, 0x69746e6573732077ull, 0x52656c6179657257ull});
            uint256_t const t2 = s1 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x6c6f774661696c75ull, 0x2c626f6f6c20616cull, 0x7320746172676574ull, 0x6528616464726573ull});
            uint256_t const t3 = s1 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0x616c6c4461746129ull, 0x2c62797465732063ull, 0x35362076616c7565ull, 0x72652c75696e7432ull});
            uint256_t const t4 = s1 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x656c617965722c61ull, 0x6464726573732072ull, 0x69746e6573732861ull, 0x52656c6179657257ull});
            uint256_t const t5 = s1 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t5, uint256_t{0x6e66745265636970ull, 0x6164647265737320ull, 0x6566756e64546f2cull, 0x6464726573732072ull});
            uint256_t const t6 = s1 + uint256_t{0xc0ull};
            aot::mstore<traits>(ctx, gas, t6, uint256_t{0x3356616c75655b5dull, 0x6174612c43616c6cull, 0x6573206d65746164ull, 0x69656e742c627974ull});
            uint256_t const t7 = s1 + uint256_t{0xe0ull};
            aot::mstore<traits>(ctx, gas, t7, uint256_t{0x73696f6e73286164ull, 0x656e5065726d6973ull, 0x6c75657329546f6bull, 0x2063616c6c335661ull});
            uint256_t const t8 = s1 + uint256_t{0x100ull};
            aot::mstore<traits>(ctx, gas, t8, uint256_t{0x6e74290000000000ull, 0x32353620616d6f75ull, 0x6b656e2c75696e74ull, 0x647265737320746full});
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6e0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x0ull}));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_6eb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6eb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x53cull};
            top[2] = uint256_t{0x6f5ull};
            top += 2;
            MONAD_AOT_TAIL return b_593<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_70f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_71b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_71b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x61, 0x81, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            top[1] = t1;
            top[2] = uint256_t{0x726ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_10e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_73d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x61, 0x47, 0x33, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x61, 0x47, 0x33, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            ctx->gas_remaining = gas;
            uint256_t r2;
            runtime::selfbalance(ctx, &r2);
            gas = ctx->gas_remaining;
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            top[0] = uint256_t{0x18ull};
            top[1] = r2;
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1967);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_76c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x92, 0x5f, 0x92, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x92, 0x5f, 0x92, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            bool const j5 = aot::nonzero(s1);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = uint256_t{0x18ull};
            top[-1] = uint256_t{0x0ull};
            top[1] = m2;
            top += 1;
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x77e); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x776);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_7af(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_e3d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_7c0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x63, 0x60, 0x52, 0x33, 0x5f, 0x52, 0x5f, 0x60, 0x60, 0x20, 0x55, 0x33, 0x7f, 0x5f, 0x80, 0xa2, 0x00}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x63, 0x60, 0x52, 0x33, 0x5f, 0x52, 0x5f, 0x60, 0x60, 0x20, 0x55, 0x33, 0x7f, 0x5f, 0x80, 0xa2, 0x00}) + 6;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 12u, 64u, 6>(ctx, gas, uint256_t{0x389a75e1ull});
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const t2 = aot::sha3_n<traits, 32>(ctx, gas, uint256_t{0xcull});
            aot::sstore<traits>(ctx, gas, t2, uint256_t{0x0ull}, (aot::gas_of<traits>({0x33, 0x7f, 0x5f, 0x80, 0xa2, 0x00}) + 0));
            uint256_t const t3 = runtime::uint256_from_address(ctx->env.sender);
            aot::log2<traits>(ctx, gas, uint256_t{0x0ull}, uint256_t{0x0ull}, uint256_t{0x17346ca6d8fe3c92ull, 0x8f9bfbae89d16759ull, 0x2cc9575ed4346446ull, 0xfa7b8eab7da67f41ull}, t3);
            gas = ctx->gas_remaining;
            aot::stop(ctx, gas);
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_804(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x80bull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x190b);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_847(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x0ull}));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_852<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_852(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x51, 0x7f, 0x81, 0x52, 0xf3}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x51, 0x7f, 0x81, 0x52, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0xbeff8ea5168af917ull, 0xee6e910560d8f8eeull, 0x48d71d25db5eb5a6ull, 0x4b21a98ca11613e8ull});
            aot::finish(ctx, gas, StatusCode::Success, t1, uint256_t{0x20ull});
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_881(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x0ull}));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_88c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_88c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x63, 0x19, 0x54, 0x60, 0x51, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x90, 0x91, 0x16, 0x81, 0x52, 0x60, 0x90, 0xf3}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x63, 0x19, 0x54, 0x60, 0x51, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x90, 0x91, 0x16, 0x81, 0x52, 0x60, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::sload<traits>(ctx, gas, uint256_t{0xffffffff74873927ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            uint256_t const t2 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t3 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore<traits>(ctx, gas, t2, t3);
            aot::finish(ctx, gas, StatusCode::Success, t2, uint256_t{0x20ull});
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_8ad(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x0ull}));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_8b8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_8b8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x51, 0x7f, 0x81, 0x52, 0xf3}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x51, 0x7f, 0x81, 0x52, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x76dfe9729e8a6cdeull, 0xed4d377e86270174ull, 0x885a8c0afe16fa80ull, 0xfd3926a097b5d365ull});
            aot::finish(ctx, gas, StatusCode::Success, t1, uint256_t{0x20ull});
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_8ee(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x61, 0x81, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            top[1] = t1;
            top[2] = uint256_t{0x8f9ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_10e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_91b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x92, 0x55, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x92, 0x55, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::sstore<traits>(ctx, gas, s1, uint256_t{0x0ull}, (aot::gas_of<traits>({0x61, 0x56}) + 0));
            top[-1] = uint256_t{0x18ull};
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1988);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_93f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x61, 0x81, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            top[1] = t1;
            top[2] = uint256_t{0x94aull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_10e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_95c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x18ull};
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1988);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_97e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x35, 0x91, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x83, 0x11, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x35, 0x91, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::calldataload(ctx, s2);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j11 = aot::nonzero(t2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[1] = m1;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_98f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_98f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0x85, 0x01, 0x94, 0x60, 0x85, 0x02, 0x01, 0x01, 0x11, 0x61, 0x57}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0x85, 0x01, 0x94, 0x60, 0x85, 0x02, 0x01, 0x01, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x20ull};
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = aot::mul(s2, uint256_t{0xe0ull});
            uint256_t const t3 = t2 + s3;
            uint256_t const t4 = t3 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            uint256_t const t5 = aot::from_bool(s0 < t4);
            bool const j12 = aot::nonzero(t5);
            top[-3] = t1;
            top += -1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_9a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9a0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9ae(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j10 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_9bf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9bf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0x9ccull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x971);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9de(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0x9ebull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_318<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a00(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0xa0dull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_318<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a32(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x98, 0x61, 0x61, 0x99, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 9, 5));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x98, 0x61, 0x61, 0x99, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s7 = top[-7];
            uint256_t const t2 = uint256_t{0x4ull} + s7;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-8] = uint256_t{0x53cull};
            top[-7] = uint256_t{0x530ull};
            top[1] = m8;
            top[2] = uint256_t{0xa46ull};
            top[3] = t1;
            top[4] = t2;
            top += 4;
            MONAD_AOT_TAIL return b_348<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a4e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0xc0ull}));
            bool const j8 = aot::nonzero(t3);
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_a5b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a5b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j10 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_a6c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a6c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0xa79ull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_318<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a79(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j11 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_a8b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a8b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0xa98ull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_318<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a98(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x90, 0x92, 0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x90, 0x92, 0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j14 = aot::nonzero(t2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = m1;
            top[-2] = m0;
            top[-1] = m2;
            top[0] = m3;
            top[1] = t1;
            top += 1;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_aad<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_aad(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0xabaull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_318<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_aba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0xac2ull};
            top += 1;
            MONAD_AOT_TAIL return b_132<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ac2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x61, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = m0;
            top[0] = m1;
            top[1] = uint256_t{0xacbull};
            top += 1;
            MONAD_AOT_TAIL return b_13f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_acb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x60, 0x35, 0x96, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x88, 0x11, 0x61, 0x57}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x60, 0x35, 0x96, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x88, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j13 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-6] = t1;
            top[-3] = m0;
            top[0] = m3;
            top[1] = m6;
            top += 1;
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_adf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_adf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x98, 0x61, 0x61, 0x99, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 9, 5));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x98, 0x61, 0x61, 0x99, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s7 = top[-7];
            uint256_t const t2 = uint256_t{0x4ull} + s7;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-8] = uint256_t{0x53cull};
            top[-7] = uint256_t{0x530ull};
            top[1] = m8;
            top[2] = uint256_t{0xaf3ull};
            top[3] = t1;
            top[4] = t2;
            top += 4;
            MONAD_AOT_TAIL return b_348<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_af3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x98, 0x90, 0x97, 0x61, 0x56}, 10, 1));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x98, 0x90, 0x97, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-9] = m0;
            top[-8] = m1;
            top[-1] = m9;
            top[0] = m8;
            MONAD_AOT_TAIL return b_14b1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b08(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j10 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_b19<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b19(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x36, 0x60, 0x82, 0x01, 0x12, 0x15, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x36, 0x60, 0x82, 0x01, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 + uint256_t{0x23ull};
            uint256_t const t3 = aot::from_bool(slt(t2, t1));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j7 = aot::nonzero(t4);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_b24<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b24(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x60, 0x01, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x60, 0x01, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x4ull} + s0;
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t2);
            bool const j12 = aot::nonzero(t3);
            top[1] = t2;
            top += 1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_b37<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b37(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x36, 0x60, 0x82, 0x60, 0x1b, 0x84, 0x01, 0x01, 0x11, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x36, 0x60, 0x82, 0x60, 0x1b, 0x84, 0x01, 0x01, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<8>(s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = s1 + t2;
            uint256_t const t4 = t3 + uint256_t{0x24ull};
            uint256_t const t5 = aot::from_bool(t1 < t4);
            bool const j10 = aot::nonzero(t5);
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_b46<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b46(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j10 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_b57<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b57(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0xb64ull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_318<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b8a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x96, 0x61, 0x96, 0x61, 0x60, 0x97, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 7, 6));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x96, 0x61, 0x96, 0x61, 0x60, 0x97, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = uint256_t{0x4ull} + s4;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-6] = uint256_t{0x53cull};
            top[-5] = uint256_t{0x530ull};
            top[-4] = uint256_t{0x24ull};
            top[1] = m6;
            top[2] = m5;
            top[3] = uint256_t{0xba1ull};
            top[4] = t1;
            top[5] = t2;
            top += 5;
            MONAD_AOT_TAIL return b_348<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_bb0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_bbc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_bbc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x61, 0x81, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            top[1] = t1;
            top[2] = uint256_t{0xbc7ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_10e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_be0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x15, 0x15, 0x03, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x15, 0x15, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = t2 - s0;
            bool const j6 = aot::nonzero(t3);
            top += -1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_be9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_be9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_bea(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x83, 0x03, 0x12, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x83, 0x03, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 - s0;
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x20ull}));
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_bf5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_bf5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x51, 0x90, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x82, 0x11, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x51, 0x90, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x82, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j11 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_c06<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c06(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x01, 0x90, 0x80, 0x60, 0x83, 0x01, 0x12, 0x15, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x01, 0x90, 0x80, 0x60, 0x83, 0x01, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            uint256_t const t2 = t1 + uint256_t{0x1full};
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = aot::from_bool(slt(t2, s2));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j9 = aot::nonzero(t4);
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[-1] = m2;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_c13<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c13(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[1] = m1;
            top[2] = uint256_t{0xc1eull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_235<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c1e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x61, 0x60, 0x51, 0x94, 0x85, 0x61, 0x56}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x61, 0x60, 0x51, 0x94, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-3] = t1;
            top[0] = m3;
            top[1] = uint256_t{0xc2cull};
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c2c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x84, 0x52, 0x60, 0x80, 0x85, 0x01, 0x91, 0x60, 0x1b, 0x83, 0x01, 0x01, 0x91, 0x83, 0x83, 0x11, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x84, 0x52, 0x60, 0x80, 0x85, 0x01, 0x91, 0x60, 0x1b, 0x83, 0x01, 0x01, 0x91, 0x83, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s3, s0);
            uint256_t const t1 = s3 + uint256_t{0x20ull};
            uint256_t const t2 = aot::shl_c<5>(s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = s1 + t2;
            uint256_t const t4 = t3 + uint256_t{0x20ull};
            uint256_t const &s2 = top[-2];
            uint256_t const t5 = aot::from_bool(s2 < t4);
            bool const j19 = aot::nonzero(t5);
            uint256_t const m1 = s1;
            top[-1] = t4;
            top[0] = t1;
            top[1] = m1;
            top += 1;
            if (j19) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_c44<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c44(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x01, 0x91}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x01, 0x91}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x20ull};
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[1] = m1;
            top += 1;
            MONAD_AOT_TAIL return b_c49<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c49(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j5) { MONAD_AOT_TAIL return b_c58<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_c51<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c51(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x90, 0x56}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint64_t const jt = aot::jump_offset(s6);
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-6] = m5;
            top += -6;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c58(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x51, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x51, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j11 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_c69<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c69(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x01, 0x90, 0x60, 0x82, 0x87, 0x03, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x01, 0x90, 0x60, 0x82, 0x87, 0x03, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s2 + s0;
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = s5 - t1;
            uint256_t const t3 = uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t2;
            uint256_t const t4 = aot::from_bool(slt(t3, uint256_t{0x40ull}));
            bool const j12 = aot::nonzero(t4);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[0] = m1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_c7a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c7a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[1] = m1;
            top[2] = uint256_t{0xc86ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_198<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c86(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x01, 0x51, 0x61, 0x81, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x01, 0x51, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x20ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            top[1] = t2;
            top[2] = uint256_t{0xc94ull};
            top[3] = t2;
            top += 3;
            MONAD_AOT_TAIL return b_be0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c94(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x52, 0x60, 0x81, 0x01, 0x51, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x52, 0x60, 0x81, 0x01, 0x51, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s3, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x40ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t2);
            bool const j15 = aot::nonzero(t3);
            top[0] = t2;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_caa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_caa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x91, 0x01, 0x01, 0x90, 0x86, 0x60, 0x83, 0x01, 0x12, 0x15, 0x61, 0x57}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x91, 0x01, 0x01, 0x90, 0x86, 0x60, 0x83, 0x01, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 + s0;
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            uint256_t const t3 = t2 + uint256_t{0x1full};
            uint256_t const &s7 = top[-7];
            uint256_t const t4 = aot::from_bool(slt(t3, s7));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            bool const j12 = aot::nonzero(t5);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t2;
            top[-1] = m2;
            top += -1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_cbb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_cbb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x51, 0x92, 0x61, 0x84, 0x61, 0x56}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x51, 0x92, 0x61, 0x84, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[1] = m2;
            top[2] = uint256_t{0xcc6ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_375<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_cc6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x51, 0x91, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x51, 0x91, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = uint256_t{0xcd3ull};
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_cd3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x81, 0x52, 0x88, 0x60, 0x86, 0x86, 0x01, 0x01, 0x11, 0x61, 0x57}, 9, 4));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x81, 0x52, 0x88, 0x60, 0x86, 0x86, 0x01, 0x01, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, s0, s4);
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + s4;
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            uint256_t const &s8 = top[-8];
            uint256_t const t3 = aot::from_bool(s8 < t2);
            bool const j12 = aot::nonzero(t3);
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_ce3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ce3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x60, 0x86, 0x81, 0x97, 0x82, 0x80, 0x98, 0x01, 0x83, 0x86, 0x01, 0x5e, 0x83, 0x01, 0x01, 0x52, 0x83, 0x82, 0x01, 0x52, 0x81, 0x52, 0x01, 0x92, 0x01, 0x91, 0x61, 0x56}, 7, 7));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x60, 0x86, 0x81, 0x97, 0x82, 0x80, 0x98, 0x01, 0x83, 0x86, 0x01, 0x5e, 0x83, 0x01, 0x01, 0x52, 0x83, 0x82, 0x01, 0x52, 0x81, 0x52, 0x01, 0x92, 0x01, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 + uint256_t{0x20ull};
            uint256_t const &s4 = top[-4];
            ctx->gas_remaining = gas;
            runtime::mcopy<traits>(ctx, &t2, &t1, &s4);
            gas = ctx->gas_remaining;
            uint256_t const t3 = s0 + s4;
            uint256_t const t4 = t3 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x0ull});
            uint256_t const &s1 = top[-1];
            uint256_t const t5 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t5, s0);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, s1);
            uint256_t const t6 = s2 + uint256_t{0x20ull};
            uint256_t const &s6 = top[-6];
            uint256_t const t7 = s6 + uint256_t{0x20ull};
            top[-6] = t7;
            top[-4] = t6;
            top += -4;
            MONAD_AOT_TAIL return b_c49<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d03(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x80, 0x60, 0x93, 0x92, 0x81, 0x84, 0x52, 0x84, 0x84, 0x01, 0x37, 0x5f, 0x82, 0x82, 0x01, 0x84, 0x01, 0x52, 0x60, 0x01, 0x60, 0x19, 0x16, 0x01, 0x01, 0x90, 0x56}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x80, 0x60, 0x93, 0x92, 0x81, 0x84, 0x52, 0x84, 0x84, 0x01, 0x37, 0x5f, 0x82, 0x82, 0x01, 0x84, 0x01, 0x52, 0x60, 0x01, 0x60, 0x19, 0x16, 0x01, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s2, s1);
            uint256_t const t1 = s2 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t1, &s0, &s1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = s1 + s2;
            uint256_t const t3 = uint256_t{0x20ull} + t2;
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0x0ull});
            uint256_t const t4 = uint256_t{0x1full} + s1;
            uint256_t const t5 = uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} & t4;
            uint256_t const t6 = t5 + s2;
            uint256_t const t7 = t6 + uint256_t{0x20ull};
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top[-3] = t7;
            top += -3;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d23(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x94, 0x92, 0x90, 0x96, 0x95, 0x93, 0x96, 0x85, 0x60, 0x84, 0x01, 0x60, 0x85, 0x52, 0x52, 0x60, 0x83, 0x01, 0x95, 0x60, 0x81, 0x60, 0x1b, 0x85, 0x01, 0x01, 0x96, 0x82, 0x5f, 0x90, 0x60, 0x19, 0x81, 0x36, 0x03, 0x01}, 8, 7));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x94, 0x92, 0x90, 0x96, 0x95, 0x93, 0x96, 0x85, 0x60, 0x84, 0x01, 0x60, 0x85, 0x52, 0x52, 0x60, 0x83, 0x01, 0x95, 0x60, 0x81, 0x60, 0x1b, 0x85, 0x01, 0x01, 0x96, 0x82, 0x5f, 0x90, 0x60, 0x19, 0x81, 0x36, 0x03, 0x01}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, s0, uint256_t{0x80ull});
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t1, s2);
            uint256_t const t2 = s0 + uint256_t{0xa0ull};
            uint256_t const t3 = aot::shl_c<5>(s2);
            uint256_t const t4 = s0 + t3;
            uint256_t const t5 = t4 + uint256_t{0xa0ull};
            uint256_t const t6 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s1 = top[-1];
            uint256_t const t7 = t6 - s1;
            uint256_t const t8 = t7 + uint256_t{0xffffffffffffff81ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const m0 = s0;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const m1 = s1;
            uint256_t const m2 = s2;
            top[-7] = m4;
            top[-6] = m7;
            top[-5] = t5;
            top[-4] = m6;
            top[-3] = m5;
            top[-2] = m0;
            top[-1] = m3;
            top[0] = m1;
            top[1] = m2;
            top[2] = t2;
            top[3] = uint256_t{0x0ull};
            top[4] = m1;
            top[5] = t8;
            top += 5;
            MONAD_AOT_TAIL return b_d4f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d4f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j5) { MONAD_AOT_TAIL return b_d93<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_d57<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d57(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x90, 0x93, 0x16, 0x60, 0x85, 0x01, 0x52, 0x50, 0x95, 0x96, 0x61, 0x96, 0x50, 0x61, 0x91, 0x50, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x60, 0x83, 0x01, 0x52, 0x56}, 13, 0));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x90, 0x93, 0x16, 0x60, 0x85, 0x01, 0x52, 0x50, 0x95, 0x96, 0x61, 0x96, 0x50, 0x61, 0x91, 0x50, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x60, 0x83, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s6 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const &s7 = top[-7];
            uint256_t const t2 = s7 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t2, t1);
            uint256_t const &s12 = top[-12];
            uint256_t const t3 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s12;
            uint256_t const t4 = s7 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            top[-12] = m11;
            top[-11] = uint256_t{0x3e1ull};
            top += -7;
            MONAD_AOT_TAIL return b_d86<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d86(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x85, 0x03, 0x91, 0x01, 0x52, 0x61, 0x56}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x85, 0x03, 0x91, 0x01, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s3 - s0;
            uint256_t const t2 = s0 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t2, t1);
            top += -1;
            MONAD_AOT_TAIL return b_d03<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d93(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x91, 0x92, 0x93, 0x94, 0x99, 0x60, 0x19, 0x88, 0x82, 0x03, 0x01, 0x85, 0x52, 0x8a, 0x35, 0x82, 0x81, 0x12, 0x15, 0x61, 0x57}, 11, 3));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x91, 0x92, 0x93, 0x94, 0x99, 0x60, 0x19, 0x88, 0x82, 0x03, 0x01, 0x85, 0x52, 0x8a, 0x35, 0x82, 0x81, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s10 = top[-10];
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = s10 - s7;
            uint256_t const t2 = t1 + uint256_t{0xffffffffffffff60ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, t2);
            uint256_t const &s5 = top[-5];
            uint256_t const t3 = aot::calldataload(ctx, s5);
            uint256_t const &s0 = top[0];
            uint256_t const t4 = aot::from_bool(slt(t3, s0));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            bool const j22 = aot::nonzero(t5);
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const m0 = s0;
            uint256_t const m10 = s10;
            top[-10] = m5;
            top[-5] = m4;
            top[-4] = m3;
            top[-3] = m2;
            top[-2] = m1;
            top[-1] = m0;
            top[0] = m10;
            top[1] = t3;
            top += 1;
            if (j22) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_dad<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_dad(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x83, 0x01, 0x80, 0x35, 0x61, 0x81, 0x61, 0x56}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x83, 0x01, 0x80, 0x35, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s3 + s0;
            uint256_t const t2 = aot::calldataload(ctx, t1);
            top[0] = t1;
            top[1] = t2;
            top[2] = uint256_t{0xdb9ull};
            top[3] = t2;
            top += 3;
            MONAD_AOT_TAIL return b_10e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_db9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x82, 0x52, 0x60, 0x81, 0x01, 0x35, 0x61, 0x81, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x82, 0x52, 0x60, 0x81, 0x01, 0x35, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s0;
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s1 + uint256_t{0x20ull};
            uint256_t const t3 = aot::calldataload(ctx, t2);
            top[0] = t3;
            top[1] = uint256_t{0xdd2ull};
            top[2] = t3;
            top += 2;
            MONAD_AOT_TAIL return b_be0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_dd2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x15, 0x60, 0x83, 0x01, 0x52, 0x60, 0x81, 0x01, 0x35, 0x60, 0x83, 0x01, 0x52, 0x60, 0x81, 0x01, 0x35, 0x60, 0x19, 0x82, 0x36, 0x03, 0x01, 0x81, 0x12, 0x15, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x15, 0x60, 0x83, 0x01, 0x52, 0x60, 0x81, 0x01, 0x35, 0x60, 0x83, 0x01, 0x52, 0x60, 0x81, 0x01, 0x35, 0x60, 0x19, 0x82, 0x36, 0x03, 0x01, 0x81, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = s2 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const &s1 = top[-1];
            uint256_t const t4 = s1 + uint256_t{0x40ull};
            uint256_t const t5 = aot::calldataload(ctx, t4);
            uint256_t const t6 = s2 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t6, t5);
            uint256_t const t7 = s1 + uint256_t{0x60ull};
            uint256_t const t8 = aot::calldataload(ctx, t7);
            uint256_t const t9 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t10 = t9 - s1;
            uint256_t const t11 = t10 + uint256_t{0xffffffffffffffe1ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t12 = aot::from_bool(slt(t8, t11));
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t12));
            bool const j29 = aot::nonzero(t13);
            top[0] = t8;
            if (j29) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_df7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_df7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x01, 0x60, 0x81, 0x35, 0x91, 0x01, 0x90, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x01, 0x60, 0x81, 0x35, 0x91, 0x01, 0x90, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const t3 = t1 + uint256_t{0x20ull};
            uint256_t const t4 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t2);
            bool const j15 = aot::nonzero(t4);
            top[-1] = t3;
            top[0] = t2;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_e0d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e0d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x36, 0x03, 0x82, 0x13, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x36, 0x03, 0x82, 0x13, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = t1 - s0;
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::from_bool(slt(t2, s1));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_e16<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e16(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x60, 0x92, 0x83, 0x92, 0x60, 0x86, 0x81, 0x60, 0x60, 0x99, 0x01, 0x52, 0x01, 0x91, 0x61, 0x56}, 3, 8));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x60, 0x92, 0x83, 0x92, 0x60, 0x86, 0x81, 0x60, 0x60, 0x99, 0x01, 0x52, 0x01, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x80ull});
            uint256_t const t2 = s2 + uint256_t{0x80ull};
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-2] = uint256_t{0x1ull};
            top[-1] = uint256_t{0x20ull};
            top[0] = uint256_t{0x20ull};
            top[1] = uint256_t{0xe2full};
            top[2] = t2;
            top[3] = m0;
            top[4] = m1;
            top += 4;
            MONAD_AOT_TAIL return b_d03<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_e2f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x9c, 0x01, 0x96, 0x95, 0x01, 0x93, 0x01, 0x91, 0x90, 0x61, 0x56}, 14, 0));
            if (MONAD_UNLIKELY(top - bottom < 14)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x9c, 0x01, 0x96, 0x95, 0x01, 0x93, 0x01, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s13 = top[-13];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s13 + s1;
            uint256_t const &s7 = top[-7];
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s7 + s2;
            uint256_t const &s6 = top[-6];
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = s6 + s3;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-13] = m0;
            top[-8] = t1;
            top[-7] = m8;
            top[-6] = t2;
            top[-5] = t3;
            top[-4] = m5;
            top[-3] = m4;
            top += -3;
            MONAD_AOT_TAIL return b_d4f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_e3d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x3d, 0x5f, 0x82, 0x3e, 0x3d, 0x90, 0xfd}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x3d, 0x5f, 0x82, 0x3e, 0x3d, 0x90, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const k6_1 = uint256_t{0x0ull};
            ctx->gas_remaining = gas;
            runtime::returndatacopy<traits>(ctx, &t1, &k6_1, &t2);
            gas = ctx->gas_remaining;
            uint256_t const t3 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            aot::finish(ctx, gas, StatusCode::Revert, t1, t3);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_e48(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x95, 0x93, 0x97, 0x96, 0x94, 0x92, 0x96, 0x60, 0x80, 0x60, 0x1b, 0x03, 0x89, 0x16, 0x15, 0x61, 0x57}, 9, 3));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x95, 0x93, 0x97, 0x96, 0x94, 0x92, 0x96, 0x60, 0x80, 0x60, 0x1b, 0x03, 0x89, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s4 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j18 = aot::nonzero(t2);
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-8] = m4;
            top[-7] = m3;
            top[-6] = m2;
            top[-5] = m7;
            top[-4] = m6;
            top[-3] = m5;
            top[-2] = m0;
            top[0] = m8;
            if (j18) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x108c); }
            MONAD_AOT_TAIL return b_e5f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e5f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x51, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x51, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            bool const j3 = aot::nonzero(t1);
            if (j3) { MONAD_AOT_TAIL return b_ee8<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_e65<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_e65(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x91, 0x61, 0x91, 0x5f, 0x95, 0x94, 0x93, 0x60, 0x51, 0x97, 0x88, 0x96, 0x87, 0x96, 0x63, 0x60, 0x1b, 0x88, 0x52, 0x60, 0x88, 0x01, 0x61, 0x56}, 9, 4));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x91, 0x61, 0x91, 0x5f, 0x95, 0x94, 0x93, 0x60, 0x51, 0x97, 0x88, 0x96, 0x87, 0x96, 0x63, 0x60, 0x1b, 0x88, 0x52, 0x60, 0x88, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xcd6e13f700000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-8] = t1;
            top[-7] = uint256_t{0x0ull};
            top[-6] = t1;
            top[-5] = t1;
            top[-4] = uint256_t{0xe8cull};
            top[-3] = m5;
            top[-2] = m4;
            top[-1] = m3;
            top[0] = m8;
            top[1] = m7;
            top[2] = m6;
            top[3] = t2;
            top += 3;
            MONAD_AOT_TAIL return b_d23<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_e8c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x03, 0x81, 0x34, 0x7f, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x5a, 0xf1, 0x90, 0x81, 0x15, 0x61, 0x57}, 5, 5));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x03, 0x81, 0x34, 0x7f, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x5a, 0xf1, 0x90, 0x81, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const t2 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t3 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xf1, 0x90, 0x81, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            auto const c12 = aot::call<traits>(ctx, gas, t3, uint256_t{0x2709c170ec4fff4full, 0xdc43a0ecde6c8b1aull, 0xb92fe925ull, 0x0ull}, t2, s2, t1, s2, s3, (aot::gas_of<traits>({0x90, 0x81, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(c12));
            bool const j17 = aot::nonzero(t4);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-4] = c12;
            top[-3] = m4;
            top += -3;
            if (j17) { MONAD_AOT_TAIL return b_7af<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_ec3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ec3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x91, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x91, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            bool const j3 = aot::nonzero(s1);
            top[-1] = uint256_t{0x0ull};
            if (j3) { MONAD_AOT_TAIL return b_ecc<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_ec9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ec9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x90, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-2] = m1;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ecc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x50, 0x3d, 0x80, 0x5f, 0x83, 0x3e, 0x61, 0x81, 0x83, 0x61, 0x56}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x50, 0x3d, 0x80, 0x5f, 0x83, 0x3e, 0x61, 0x81, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const k8_1 = uint256_t{0x0ull};
            ctx->gas_remaining = gas;
            runtime::returndatacopy<traits>(ctx, &s0, &k8_1, &t1);
            gas = ctx->gas_remaining;
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x3e1ull};
            top[1] = t1;
            top[2] = uint256_t{0xee0ull};
            top[3] = t1;
            top[4] = m0;
            top += 4;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ee0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x01, 0x90, 0x61, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x01, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 + s0;
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[0] = m1;
            MONAD_AOT_TAIL return b_bea<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ee8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x96, 0x93, 0x94, 0x95, 0x98, 0x90, 0x92, 0x97, 0x61, 0x61, 0x36, 0x89, 0x89, 0x61, 0x56}, 10, 6));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x96, 0x93, 0x94, 0x95, 0x98, 0x90, 0x92, 0x97, 0x61, 0x61, 0x36, 0x89, 0x89, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-9] = m6;
            top[-8] = m3;
            top[-7] = m2;
            top[-6] = m5;
            top[-5] = m4;
            top[-4] = m7;
            top[-3] = m1;
            top[-2] = m0;
            top[-1] = m9;
            top[0] = m8;
            top[1] = uint256_t{0xf12ull};
            top[2] = uint256_t{0xeffull};
            top[3] = t1;
            top[4] = m5;
            top[5] = m4;
            top += 5;
            MONAD_AOT_TAIL return b_390<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_eff(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x36, 0x88, 0x8e, 0x61, 0x56}, 12, 5));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x36, 0x88, 0x8e, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            top[1] = uint256_t{0xf0aull};
            top[2] = t1;
            top[3] = m6;
            top[4] = m11;
            top += 4;
            MONAD_AOT_TAIL return b_1164<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f0a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x8b, 0x84, 0x61, 0x56}, 12, 3));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x8b, 0x84, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-1] = m0;
            top[0] = m1;
            top[1] = m11;
            top[2] = m3;
            top += 2;
            MONAD_AOT_TAIL return b_19c5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f12(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x85, 0x51, 0x51, 0x61, 0x56}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x85, 0x51, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s4);
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            top[1] = uint256_t{0xf1dull};
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_1786<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f1d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x95, 0x5f, 0x9b, 0x7f, 0x9c}, 12, 2));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x95, 0x5f, 0x9b, 0x7f, 0x9c}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            top[-11] = uint256_t{0x2709c170ec4fff4full, 0xdc43a0ecde6c8b1aull, 0xb92fe925ull, 0x0ull};
            top[-6] = m0;
            top[0] = m6;
            top[1] = m11;
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_f43<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f43(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x87, 0x51, 0x80, 0x51, 0x82, 0x10, 0x15, 0x61, 0x57}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x87, 0x51, 0x80, 0x51, 0x82, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s7);
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s0 = top[0];
            uint256_t const t3 = aot::from_bool(s0 < t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j9 = aot::nonzero(t4);
            top[1] = t1;
            top += 1;
            if (j9) { MONAD_AOT_TAIL return b_fe0<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_f4f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f4f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x5f, 0x51, 0x60, 0x61, 0x5f, 0x39, 0x5f, 0x51, 0x90, 0x5f, 0x52, 0x8f, 0x8e, 0x61, 0x8f, 0x8f, 0x8f, 0x8f, 0x61, 0x89, 0x61, 0x92, 0x61, 0x82, 0x60, 0x60, 0x9f, 0x82, 0x61, 0x91, 0x61, 0x56}, 15, 18));
            if (MONAD_UNLIKELY(top - bottom < 15)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1006)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x5f, 0x51, 0x60, 0x61, 0x5f, 0x39, 0x5f, 0x51, 0x90, 0x5f, 0x52, 0x8f, 0x8e, 0x61, 0x8f, 0x8f, 0x8f, 0x8f, 0x61, 0x89, 0x61, 0x92, 0x61, 0x82, 0x60, 0x60, 0x9f, 0x82, 0x61, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k6_0 = uint256_t{0x0ull};
            uint256_t const k6_1 = uint256_t{0x1e22ull};
            uint256_t const k6_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k6_0, &k6_1, &k6_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s14 = top[-14];
            uint256_t const m14 = s14;
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x1ull};
            top[0] = m1;
            top[1] = t2;
            top[2] = m14;
            top[3] = m12;
            top[4] = uint256_t{0xfd7ull};
            top[5] = m11;
            top[6] = m10;
            top[7] = m9;
            top[8] = uint256_t{0xfcbull};
            top[9] = uint256_t{0xfbdull};
            top[10] = m1;
            top[11] = m8;
            top[12] = uint256_t{0xfb6ull};
            top[13] = m1;
            top[14] = uint256_t{0x20ull};
            top[15] = uint256_t{0xf81ull};
            top[16] = m1;
            top[17] = m0;
            top += 17;
            MONAD_AOT_TAIL return b_17e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f81(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x01, 0x51, 0x96, 0x8c, 0x61, 0x61, 0x61, 0x56}, 14, 3));
            if (MONAD_UNLIKELY(top - bottom < 14)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x01, 0x51, 0x96, 0x8c, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 + s1;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s13 = top[-13];
            uint256_t const m13 = s13;
            top[-8] = t3;
            top[-1] = m8;
            top[0] = m13;
            top[1] = uint256_t{0xfa0ull};
            top[2] = uint256_t{0xf91ull};
            top += 2;
            MONAD_AOT_TAIL return b_226<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f91(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x90, 0x92, 0x16, 0x82, 0x52, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x90, 0x92, 0x16, 0x82, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, t1);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fa0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x88, 0x60, 0x82, 0x01, 0x52, 0x61, 0x83, 0x83, 0x61, 0x56}, 9, 4));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x88, 0x60, 0x82, 0x01, 0x52, 0x61, 0x83, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x20ull};
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, t1, s8);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0xfb0ull};
            top[2] = m2;
            top[3] = m1;
            top += 3;
            MONAD_AOT_TAIL return b_17e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fb0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x52, 0x61, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s0, s1);
            top += -2;
            MONAD_AOT_TAIL return b_17e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fb6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x51, 0x61, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            top[-1] = t1;
            top += -1;
            MONAD_AOT_TAIL return b_17e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fbd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x51, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x90, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x51, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t2;
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top[-1] = t3;
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fcb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x96, 0x87, 0x96, 0x87, 0x61, 0x56}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x96, 0x87, 0x96, 0x87, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-6] = t1;
            top[-5] = t1;
            top[1] = m6;
            top[2] = m5;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_122b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fd7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x03, 0x90, 0xa1, 0x01, 0x61, 0x56}, 6, 0));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x03, 0x90, 0xa1, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            ctx->gas_remaining = gas;
            runtime::log1<traits>(ctx, &s2, &t1, &s3);
            gas = ctx->gas_remaining;
            uint256_t const &s4 = top[-4];
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = s4 + s5;
            top[-5] = t2;
            top += -5;
            MONAD_AOT_TAIL return b_f43<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fe0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x97, 0x94, 0x91, 0x99, 0x92, 0x9a, 0x96, 0x90, 0x98, 0x95, 0x93, 0x9b, 0x50, 0x60, 0x80, 0x60, 0x1b, 0x03, 0x7f, 0x16, 0x91, 0x61, 0x61, 0x56}, 15, 0));
            if (MONAD_UNLIKELY(top - bottom < 15)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x97, 0x94, 0x91, 0x99, 0x92, 0x9a, 0x96, 0x90, 0x98, 0x95, 0x93, 0x9b, 0x50, 0x60, 0x80, 0x60, 0x1b, 0x03, 0x7f, 0x16, 0x91, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s13 = top[-13];
            uint256_t const m13 = s13;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[-14] = m6;
            top[-13] = m5;
            top[-12] = m4;
            top[-11] = m3;
            top[-10] = m2;
            top[-9] = m13;
            top[-8] = m11;
            top[-7] = m10;
            top[-6] = m8;
            top[-5] = m12;
            top[-4] = uint256_t{0xdee9f6b43ac78ba3ull, 0x22d473030f116dull, 0x0ull, 0x0ull};
            top[-3] = m9;
            top[-2] = m7;
            top[-1] = uint256_t{0x1021ull};
            top += -1;
            MONAD_AOT_TAIL return b_593<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1021(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x94, 0x83, 0x3b, 0x15, 0x61, 0x57}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x94, 0x83, 0x3b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            ctx->gas_remaining = gas;
            uint256_t r3;
            runtime::extcodesize<traits>(ctx, &r3, &s3);
            gas = ctx->gas_remaining;
            uint256_t const t1 = aot::from_bool(!aot::nonzero(r3));
            bool const j6 = aot::nonzero(t1);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-5] = m0;
            top[0] = m5;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_102a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_102a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x5f, 0x96, 0x92, 0x87, 0x93, 0x60, 0x51, 0x9e, 0x8f, 0x98, 0x89, 0x97, 0x88, 0x96, 0x63, 0x60, 0x1b, 0x88, 0x52, 0x60, 0x88, 0x01, 0x61, 0x56}, 12, 9));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x5f, 0x96, 0x92, 0x87, 0x93, 0x60, 0x51, 0x9e, 0x8f, 0x98, 0x89, 0x97, 0x88, 0x96, 0x63, 0x60, 0x1b, 0x88, 0x52, 0x60, 0x88, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xfe8ec1a700000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-11] = t1;
            top[-5] = uint256_t{0x0ull};
            top[-4] = t1;
            top[-2] = t1;
            top[-1] = uint256_t{0x0ull};
            top[0] = t1;
            top[1] = uint256_t{0x104eull};
            top[2] = m1;
            top[3] = m5;
            top[4] = m11;
            top[5] = m4;
            top[6] = m2;
            top[7] = m0;
            top[8] = t2;
            top += 8;
            MONAD_AOT_TAIL return b_1844<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_104e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x03, 0x92, 0x5a, 0xf1, 0x92, 0x83, 0x15, 0x61, 0x57}, 10, 0));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x03, 0x92, 0x5a, 0xf1, 0x92, 0x83, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xf1, 0x92, 0x83, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const &s4 = top[-4];
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            uint256_t const &s5 = top[-5];
            uint256_t const &s6 = top[-6];
            auto const c4 = aot::call<traits>(ctx, gas, t2, s4, s2, s3, t1, s5, s6, (aot::gas_of<traits>({0x92, 0x83, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t3 = aot::from_bool(!aot::nonzero(c4));
            bool const j9 = aot::nonzero(t3);
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[-9] = c4;
            top[-6] = m9;
            top += -6;
            if (j9) { MONAD_AOT_TAIL return b_7af<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_105a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_105a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x96, 0x61, 0x94, 0x61, 0x57}, 7, 3));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x96, 0x61, 0x94, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            bool const j5 = aot::nonzero(s3);
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-6] = uint256_t{0x0ull};
            top[-3] = uint256_t{0xe8cull};
            top[1] = m6;
            top += 1;
            if (j5) { MONAD_AOT_TAIL return b_1072<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1064<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1064(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x93, 0x95, 0x96, 0x97, 0x50, 0x82, 0x94, 0x50, 0x61, 0x56}, 8, 1));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x93, 0x95, 0x96, 0x97, 0x50, 0x82, 0x94, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-7] = m6;
            top[-6] = m5;
            top[-5] = m3;
            top[-4] = m2;
            top[-3] = m1;
            MONAD_AOT_TAIL return b_e65<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1072(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x89, 0x61, 0x93, 0x61, 0x56}, 8, 5));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x89, 0x61, 0x93, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[0] = uint256_t{0x1086ull};
            top[1] = m0;
            top[2] = uint256_t{0x1080ull};
            top[3] = m7;
            top[4] = m0;
            top += 4;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1080(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_540<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1086(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_1064<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10a7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x51, 0x90, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x51, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top[-1] = t1;
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10c8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x02, 0x01, 0x90, 0x56}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x02, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(uint256_t{0xe0ull}, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 + s1;
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t2;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10e0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10ec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = uint256_t{0xc0ull};
            top[2] = m0;
            top[3] = uint256_t{0x10faull};
            top[4] = t1;
            top += 4;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b3);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_114a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x90, 0x81, 0x10, 0x15, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x90, 0x81, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s2 < s1);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[-1] = m2;
            top += -1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x10ce); }
            MONAD_AOT_TAIL return b_1154<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1154(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1b, 0x01, 0x90, 0x56}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1b, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 + s1;
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t2;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_115a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x35, 0x61, 0x81, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x35, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            top[0] = t1;
            top[1] = uint256_t{0x3e1ull};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_10e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1164(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x91, 0x90, 0x92, 0x61, 0x84, 0x61, 0x56}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x91, 0x90, 0x92, 0x61, 0x84, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-3] = m1;
            top[-2] = m3;
            top[-1] = m2;
            top[1] = uint256_t{0x1171ull};
            top[2] = m1;
            top += 2;
            MONAD_AOT_TAIL return b_235<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1171(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x93, 0x61, 0x60, 0x51, 0x95, 0x86, 0x61, 0x56}, 5, 4));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x93, 0x61, 0x60, 0x51, 0x95, 0x86, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-4] = t1;
            top[0] = m4;
            top[1] = uint256_t{0x117full};
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_117f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x85, 0x82, 0x81, 0x52, 0x01, 0x90, 0x60, 0x1b, 0x82, 0x01, 0x91, 0x83, 0x83, 0x11, 0x61, 0x57}, 5, 4));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x85, 0x82, 0x81, 0x52, 0x01, 0x90, 0x60, 0x1b, 0x82, 0x01, 0x91, 0x83, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s4, s0);
            uint256_t const t1 = s4 + uint256_t{0x20ull};
            uint256_t const t2 = aot::shl_c<5>(s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = s1 + t2;
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = aot::from_bool(s2 < t3);
            bool const j17 = aot::nonzero(t4);
            uint256_t const m1 = s1;
            top[-1] = t3;
            top[0] = t1;
            top[1] = m1;
            top += 1;
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_1195<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1195(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x91}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x91}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = m0;
            top[1] = m1;
            top += 1;
            MONAD_AOT_TAIL return b_1197<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1197(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j5) { MONAD_AOT_TAIL return b_11a5<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_119f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_119f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x56}, 6, 0));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint64_t const jt = aot::jump_offset(s5);
            top += -6;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_11a5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x35, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::calldataload(ctx, s2);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j11 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_11b6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11b6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x01, 0x60, 0x81, 0x87, 0x03, 0x12, 0x61, 0x57}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x01, 0x60, 0x81, 0x87, 0x03, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s2 + s0;
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = s5 - t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x80ull}));
            bool const j8 = aot::nonzero(t3);
            top[0] = t1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_11c2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11c2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[1] = m1;
            top[2] = uint256_t{0x11ceull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_1ce<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_11ce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x35, 0x61, 0x81, 0x61, 0x56}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x35, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::calldataload(ctx, s1);
            top[1] = t1;
            top[2] = uint256_t{0x11d9ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_10e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_11d9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x52, 0x60, 0x82, 0x01, 0x35, 0x61, 0x81, 0x61, 0x56}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x52, 0x60, 0x82, 0x01, 0x35, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s3, s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0x20ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            top[0] = t2;
            top[1] = uint256_t{0x11e9ull};
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_be0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_11e9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x84, 0x01, 0x52, 0x60, 0x82, 0x01, 0x35, 0x60, 0x84, 0x01, 0x52, 0x60, 0x82, 0x01, 0x35, 0x92, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x84, 0x11, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x84, 0x01, 0x52, 0x60, 0x82, 0x01, 0x35, 0x60, 0x84, 0x01, 0x52, 0x60, 0x82, 0x01, 0x35, 0x92, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x84, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s2 + uint256_t{0x40ull};
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const t4 = s3 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const t5 = s2 + uint256_t{0x60ull};
            uint256_t const t6 = aot::calldataload(ctx, t5);
            uint256_t const t7 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t6);
            bool const j26 = aot::nonzero(t7);
            uint256_t const m3 = s3;
            top[-3] = t6;
            top[0] = m3;
            if (j26) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_120d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_120d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x88, 0x60, 0x95, 0x86, 0x95, 0x01, 0x61, 0x56}, 8, 4));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x88, 0x60, 0x95, 0x86, 0x95, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s2 + s3;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[-3] = uint256_t{0x20ull};
            top[-2] = uint256_t{0x20ull};
            top[1] = uint256_t{0x121bull};
            top[2] = m7;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_3c6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_121b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x01, 0x52, 0x81, 0x52, 0x01, 0x92, 0x01, 0x91, 0x61, 0x56}, 7, 2));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x01, 0x52, 0x81, 0x52, 0x01, 0x92, 0x01, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x60ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, s1);
            uint256_t const &s3 = top[-3];
            uint256_t const t2 = s2 + s3;
            uint256_t const &s6 = top[-6];
            uint256_t const &s4 = top[-4];
            uint256_t const t3 = s6 + s4;
            top[-6] = t3;
            top[-4] = t2;
            top += -4;
            MONAD_AOT_TAIL return b_1197<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_122b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x91, 0x82, 0x16, 0x81, 0x52, 0x91, 0x81, 0x16, 0x60, 0x83, 0x01, 0x52, 0x90, 0x91, 0x16, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x60, 0x82, 0x01, 0x81, 0x90, 0x52, 0x61, 0x93, 0x91, 0x01, 0x91, 0x61, 0x56}, 7, 3));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x91, 0x82, 0x16, 0x81, 0x52, 0x91, 0x81, 0x16, 0x60, 0x83, 0x01, 0x52, 0x90, 0x91, 0x16, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x60, 0x82, 0x01, 0x81, 0x90, 0x52, 0x61, 0x93, 0x91, 0x01, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s1;
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, t1);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s2;
            uint256_t const t3 = s0 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const &s3 = top[-3];
            uint256_t const t4 = s3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t5 = s0 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const t6 = s0 + uint256_t{0x60ull};
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, t6, s4);
            uint256_t const t7 = s0 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t7, uint256_t{0xa0ull});
            uint256_t const t8 = s0 + uint256_t{0xa0ull};
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-6] = uint256_t{0x3e1ull};
            top[-5] = t8;
            top[-4] = m6;
            top[-3] = m5;
            top += -3;
            MONAD_AOT_TAIL return b_d03<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1277(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x60, 0x1b, 0x03, 0x89, 0x16, 0x15, 0x61, 0x57}, 9, 3));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x60, 0x1b, 0x03, 0x89, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = s8 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x108c); }
            MONAD_AOT_TAIL return b_1286<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1286(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x97, 0x92, 0x5f}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x97, 0x92, 0x5f}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-7] = uint256_t{0x2709c170ec4fff4full, 0xdc43a0ecde6c8b1aull, 0xb92fe925ull, 0x0ull};
            top[-2] = m7;
            top[1] = m2;
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x12aa);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12b3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x5f, 0x95, 0x94, 0x93, 0x92, 0x91, 0x61, 0x91, 0x60, 0x51, 0x98, 0x89, 0x97, 0x88, 0x96, 0x87, 0x96, 0x63, 0x60, 0x1b, 0x88, 0x52, 0x60, 0x88, 0x01, 0x61, 0x56}, 13, 2));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x5f, 0x95, 0x94, 0x93, 0x92, 0x91, 0x61, 0x91, 0x60, 0x51, 0x98, 0x89, 0x97, 0x88, 0x96, 0x87, 0x96, 0x63, 0x60, 0x1b, 0x88, 0x52, 0x60, 0x88, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xcd6e13f700000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-12] = t1;
            top[-11] = uint256_t{0x0ull};
            top[-10] = t1;
            top[-9] = m10;
            top[-8] = t1;
            top[-7] = t1;
            top[-6] = uint256_t{0x12dfull};
            top[-5] = m7;
            top[-4] = m6;
            top[-3] = m12;
            top[-2] = m11;
            top[-1] = m9;
            top[0] = m8;
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_d23<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_12df(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x03, 0x91, 0x34, 0x90, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x5a, 0xf1, 0x90, 0x81, 0x15, 0x61, 0x57}, 7, 3));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x03, 0x91, 0x34, 0x90, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x5a, 0xf1, 0x90, 0x81, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const t2 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s3;
            uint256_t const t4 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xf1, 0x90, 0x81, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const &s2 = top[-2];
            uint256_t const &s4 = top[-4];
            uint256_t const &s5 = top[-5];
            auto const c12 = aot::call<traits>(ctx, gas, t4, t3, t2, s2, t1, s4, s5, (aot::gas_of<traits>({0x90, 0x81, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t5 = aot::from_bool(!aot::nonzero(c12));
            bool const j17 = aot::nonzero(t5);
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-6] = c12;
            top[-5] = m6;
            top += -5;
            if (j17) { MONAD_AOT_TAIL return b_7af<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_12f6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12f6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x91, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x91, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            bool const j3 = aot::nonzero(s1);
            top[-1] = uint256_t{0x0ull};
            if (j3) { MONAD_AOT_TAIL return b_ecc<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_12fc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12fc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x90, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-2] = m1;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1333(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_115a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1338(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x90, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s0;
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top[-1] = t1;
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_13a5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x63, 0x60, 0x1b, 0x81, 0x52, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x93, 0x90, 0x93, 0x16, 0x60, 0x84, 0x01, 0x52, 0x30, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x94, 0x90, 0x94, 0x52, 0x60, 0x82, 0x01, 0x95, 0x90, 0x95, 0x52, 0x60, 0x81, 0x01, 0x99, 0x90, 0x99, 0x52, 0x60, 0x89, 0x01, 0x93, 0x90, 0x93, 0x52, 0x60, 0x90, 0x92, 0x16, 0x60, 0x88, 0x01, 0x52, 0x60, 0x87, 0x01, 0x92, 0x90, 0x92, 0x52, 0x61, 0x86, 0x01, 0x52, 0x5f, 0x90, 0x85, 0x90, 0x61, 0x90, 0x82, 0x90, 0x84, 0x90, 0x5a, 0xf1, 0x91, 0x82, 0x15, 0x61, 0x57}, 12, 4));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x63, 0x60, 0x1b, 0x81, 0x52, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x93, 0x90, 0x93, 0x16, 0x60, 0x84, 0x01, 0x52, 0x30, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x94, 0x90, 0x94, 0x52, 0x60, 0x82, 0x01, 0x95, 0x90, 0x95, 0x52, 0x60, 0x81, 0x01, 0x99, 0x90, 0x99, 0x52, 0x60, 0x89, 0x01, 0x93, 0x90, 0x93, 0x52, 0x60, 0x90, 0x92, 0x16, 0x60, 0x88, 0x01, 0x52, 0x60, 0x87, 0x01, 0x92, 0x90, 0x92, 0x52, 0x61, 0x86, 0x01, 0x52, 0x5f, 0x90, 0x85, 0x90, 0x61, 0x90, 0x82, 0x90, 0x84, 0x90, 0x5a, 0xf1, 0x91, 0x82, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xef55bec600000000ull});
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s2;
            uint256_t const t3 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t5 = t1 + uint256_t{0x24ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const t6 = t1 + uint256_t{0x44ull};
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, t6, s4);
            uint256_t const t7 = t1 + uint256_t{0x64ull};
            uint256_t const &s6 = top[-6];
            aot::mstore<traits>(ctx, gas, t7, s6);
            uint256_t const t8 = t1 + uint256_t{0x84ull};
            uint256_t const &s11 = top[-11];
            aot::mstore<traits>(ctx, gas, t8, s11);
            uint256_t const t9 = t1 + uint256_t{0xa4ull};
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t9, s1);
            uint256_t const &s3 = top[-3];
            uint256_t const t10 = s3 & uint256_t{0xffull};
            uint256_t const t11 = t1 + uint256_t{0xc4ull};
            aot::mstore<traits>(ctx, gas, t11, t10);
            uint256_t const t12 = t1 + uint256_t{0xe4ull};
            uint256_t const &s7 = top[-7];
            aot::mstore<traits>(ctx, gas, t12, s7);
            uint256_t const t13 = t1 + uint256_t{0x104ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t13, s0);
            uint256_t const t14 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xf1, 0x91, 0x82, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const &s5 = top[-5];
            auto const c83 = aot::call<traits>(ctx, gas, t14, s5, uint256_t{0x0ull}, t1, uint256_t{0x124ull}, t1, uint256_t{0x0ull}, (aot::gas_of<traits>({0x91, 0x82, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t15 = aot::from_bool(!aot::nonzero(c83));
            bool const j88 = aot::nonzero(t15);
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[-11] = t1;
            top[-9] = c83;
            top[-7] = m9;
            top += -7;
            if (j88) { MONAD_AOT_TAIL return b_7af<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1416<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1416(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x8b, 0x8f, 0x93, 0x8a, 0x93, 0x61, 0x61, 0x8f, 0x93, 0x8d, 0x61, 0x8c, 0x92, 0x61, 0x60, 0x9f, 0x61, 0x5f, 0x51, 0x60, 0x61, 0x5f, 0x39, 0x5f, 0x51, 0x90, 0x5f, 0x52, 0x9f, 0x87, 0x8f, 0x88, 0x90, 0x61, 0x95, 0x61, 0x94, 0x61, 0x57}, 14, 20));
            if (MONAD_UNLIKELY(top - bottom < 14)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1004)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x8b, 0x8f, 0x93, 0x8a, 0x93, 0x61, 0x61, 0x8f, 0x93, 0x8d, 0x61, 0x8c, 0x92, 0x61, 0x60, 0x9f, 0x61, 0x5f, 0x51, 0x60, 0x61, 0x5f, 0x39, 0x5f, 0x51, 0x90, 0x5f, 0x52, 0x9f, 0x87, 0x8f, 0x88, 0x90, 0x61, 0x95, 0x61, 0x94, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k23_0 = uint256_t{0x0ull};
            uint256_t const k23_1 = uint256_t{0x1e22ull};
            uint256_t const k23_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k23_0, &k23_1, &k23_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const &s2 = top[-2];
            bool const j39 = aot::nonzero(s2);
            uint256_t const &s13 = top[-13];
            uint256_t const m13 = s13;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-4] = uint256_t{0x1ull};
            top[-2] = t2;
            top[-1] = m13;
            top[0] = m7;
            top[1] = uint256_t{0x1485ull};
            top[2] = m10;
            top[3] = m9;
            top[4] = m0;
            top[5] = uint256_t{0x1476ull};
            top[6] = uint256_t{0x1333ull};
            top[7] = m3;
            top[8] = m6;
            top[9] = uint256_t{0x1470ull};
            top[10] = m1;
            top[11] = uint256_t{0x1463ull};
            top[12] = uint256_t{0x145aull};
            top[13] = uint256_t{0x1338ull};
            top[14] = uint256_t{0x1333ull};
            top[15] = m3;
            top[16] = m6;
            top[17] = m7;
            top[18] = m4;
            top += 18;
            if (j39) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x148e); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1454);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_14b1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x95, 0x96, 0x97, 0x92, 0x99, 0x98, 0x93, 0x99, 0x91, 0x90, 0x91, 0x80, 0x83, 0x03, 0x61, 0x57}, 11, 2));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x95, 0x96, 0x97, 0x92, 0x99, 0x98, 0x93, 0x99, 0x91, 0x90, 0x91, 0x80, 0x83, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s1 - s3;
            bool const j16 = aot::nonzero(t1);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const m1 = s1;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const m3 = s3;
            top[-10] = m4;
            top[-9] = m10;
            top[-8] = m7;
            top[-7] = m6;
            top[-6] = m0;
            top[-4] = m9;
            top[-3] = m8;
            top[-2] = m1;
            top[-1] = m2;
            top[0] = m3;
            if (j16) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x14a2); }
            MONAD_AOT_TAIL return b_14c4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14c4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x60, 0x1b, 0x03, 0x88, 0x16, 0x15, 0x61, 0x57}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x60, 0x1b, 0x03, 0x88, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = s7 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x108c); }
            MONAD_AOT_TAIL return b_14d3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14d3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x96, 0x92, 0x5f}, 7, 2));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x96, 0x92, 0x5f}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-6] = uint256_t{0x2709c170ec4fff4full, 0xdc43a0ecde6c8b1aull, 0xb92fe925ull, 0x0ull};
            top[-2] = m6;
            top[1] = m2;
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_14f7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_14f7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x81, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s0 < s1);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1529<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_14ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14ff(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x5f, 0x95, 0x96, 0x97, 0x91, 0x61, 0x91, 0x60, 0x51, 0x98, 0x89, 0x97, 0x88, 0x96, 0x87, 0x96, 0x63, 0x60, 0x1b, 0x88, 0x52, 0x60, 0x88, 0x01, 0x61, 0x56}, 13, 3));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x5f, 0x95, 0x96, 0x97, 0x91, 0x61, 0x91, 0x60, 0x51, 0x98, 0x89, 0x97, 0x88, 0x96, 0x87, 0x96, 0x63, 0x60, 0x1b, 0x88, 0x52, 0x60, 0x88, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xcd6e13f700000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            top[-12] = m11;
            top[-11] = t1;
            top[-10] = uint256_t{0x0ull};
            top[-9] = t1;
            top[-7] = t1;
            top[-6] = t1;
            top[-5] = uint256_t{0x12dfull};
            top[-4] = m6;
            top[-3] = m5;
            top[-2] = m10;
            top[-1] = m9;
            top[0] = m7;
            top[1] = m12;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_d23<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1529(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x61, 0x61, 0x61, 0x60, 0x95, 0x87, 0x8b, 0x61, 0x56}, 5, 9));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x61, 0x61, 0x61, 0x60, 0x95, 0x87, 0x8b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[0] = uint256_t{0x1ull};
            top[1] = m0;
            top[2] = uint256_t{0x1555ull};
            top[3] = uint256_t{0x1540ull};
            top[4] = uint256_t{0x1338ull};
            top[5] = uint256_t{0x1333ull};
            top[6] = m0;
            top[7] = m1;
            top[8] = m4;
            top += 8;
            MONAD_AOT_TAIL return b_114a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1540(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x8b, 0x61, 0x84, 0x88, 0x8a, 0x61, 0x56}, 12, 6));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x8b, 0x61, 0x84, 0x88, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[1] = m11;
            top[2] = uint256_t{0x154cull};
            top[3] = m2;
            top[4] = m5;
            top[5] = m6;
            top += 5;
            MONAD_AOT_TAIL return b_114a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_154c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x35, 0x91, 0x33, 0x90, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x35, 0x91, 0x33, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[0] = t2;
            top[1] = m2;
            top += 1;
            MONAD_AOT_TAIL return b_1b45<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1555(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x51, 0x60, 0x61, 0x5f, 0x39, 0x5f, 0x51, 0x90, 0x5f, 0x52, 0x61, 0x61, 0x83, 0x86, 0x8a, 0x61, 0x56}, 6, 7));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x51, 0x60, 0x61, 0x5f, 0x39, 0x5f, 0x51, 0x90, 0x5f, 0x52, 0x61, 0x61, 0x83, 0x86, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k6_0 = uint256_t{0x0ull};
            uint256_t const k6_1 = uint256_t{0x1e22ull};
            uint256_t const k6_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k6_0, &k6_1, &k6_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[1] = t2;
            top[2] = uint256_t{0x1571ull};
            top[3] = uint256_t{0x1333ull};
            top[4] = m0;
            top[5] = m2;
            top[6] = m5;
            top += 6;
            MONAD_AOT_TAIL return b_114a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1571(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x8b, 0x61, 0x8b, 0x8b, 0x61, 0x87, 0x8b, 0x8d, 0x61, 0x56}, 12, 9));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x8b, 0x61, 0x8b, 0x8b, 0x61, 0x87, 0x8b, 0x8d, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[1] = m11;
            top[2] = uint256_t{0x1590ull};
            top[3] = m9;
            top[4] = m8;
            top[5] = uint256_t{0x1582ull};
            top[6] = m2;
            top[7] = m5;
            top[8] = m6;
            top += 8;
            MONAD_AOT_TAIL return b_114a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1582(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x35, 0x60, 0x51, 0x95, 0x86, 0x95, 0x33, 0x87, 0x61, 0x56}, 6, 5));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x35, 0x60, 0x51, 0x95, 0x86, 0x95, 0x33, 0x87, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const t2 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t3 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-5] = t2;
            top[-4] = t2;
            top[0] = t1;
            top[1] = m5;
            top[2] = m4;
            top[3] = t3;
            top[4] = t2;
            top += 4;
            MONAD_AOT_TAIL return b_122b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1590(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x03, 0x90, 0xa1, 0x01, 0x61, 0x56}, 6, 0));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x03, 0x90, 0xa1, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            ctx->gas_remaining = gas;
            runtime::log1<traits>(ctx, &s2, &t1, &s3);
            gas = ctx->gas_remaining;
            uint256_t const &s4 = top[-4];
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = s4 + s5;
            top[-5] = t2;
            top += -5;
            MONAD_AOT_TAIL return b_14f7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_15a3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1b, 0x01, 0x90, 0x56}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1b, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<8>(s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 + s1;
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t2;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_15b5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = uint256_t{0xe0ull};
            top[2] = m0;
            top[3] = uint256_t{0x15c3ull};
            top[4] = t1;
            top += 4;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1e9);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_163b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x94, 0x90, 0x5f}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x94, 0x90, 0x5f}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-4] = uint256_t{0x2709c170ec4fff4full, 0xdc43a0ecde6c8b1aull, 0xb92fe925ull, 0x0ull};
            top[0] = m4;
            top[1] = m0;
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x165f);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1667(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x60, 0x51, 0x63, 0x60, 0x1b, 0x81, 0x52, 0x97, 0x98, 0x5f, 0x97, 0x89, 0x97, 0x88, 0x96, 0x87, 0x96, 0x61, 0x96, 0x94, 0x95, 0x50, 0x60, 0x88, 0x01, 0x61, 0x56}, 11, 5));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x60, 0x51, 0x63, 0x60, 0x1b, 0x81, 0x52, 0x97, 0x98, 0x5f, 0x97, 0x89, 0x97, 0x88, 0x96, 0x87, 0x96, 0x61, 0x96, 0x94, 0x95, 0x50, 0x60, 0x88, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xcd6e13f700000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-10] = m9;
            top[-9] = t1;
            top[-8] = uint256_t{0x0ull};
            top[-7] = t1;
            top[-5] = t1;
            top[-4] = t1;
            top[-3] = uint256_t{0x12dfull};
            top[-2] = m10;
            top[-1] = m3;
            top[0] = m8;
            top[1] = m7;
            top[2] = m5;
            top[3] = m4;
            top[4] = t2;
            top += 4;
            MONAD_AOT_TAIL return b_d23<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_16c6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x88, 0x81, 0x61, 0x8f, 0x89, 0x60, 0x97, 0x61, 0x61, 0x61, 0x5f, 0x51, 0x60, 0x61, 0x5f, 0x39, 0x5f, 0x51, 0x90, 0x5f, 0x52, 0x99, 0x51, 0x60, 0x80, 0x60, 0x1b, 0x03, 0x16, 0x90, 0x56}, 13, 13));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1011)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x88, 0x81, 0x61, 0x8f, 0x89, 0x60, 0x97, 0x61, 0x61, 0x61, 0x5f, 0x51, 0x60, 0x61, 0x5f, 0x39, 0x5f, 0x51, 0x90, 0x5f, 0x52, 0x99, 0x51, 0x60, 0x80, 0x60, 0x1b, 0x03, 0x16, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k15_0 = uint256_t{0x0ull};
            uint256_t const k15_1 = uint256_t{0x1e22ull};
            uint256_t const k15_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k15_0, &k15_1, &k15_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const &s0 = top[0];
            uint256_t const t3 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t4 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t3;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const m0 = s0;
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = uint256_t{0x1ull};
            top[0] = t2;
            top[1] = m8;
            top[2] = m0;
            top[3] = uint256_t{0x176full};
            top[4] = m12;
            top[5] = m5;
            top[6] = m2;
            top[7] = uint256_t{0x1476ull};
            top[8] = uint256_t{0x1761ull};
            top[9] = t4;
            top += 9;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x16f3);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1786(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x61, 0x82, 0x61, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = m0;
            top[0] = m1;
            top[1] = uint256_t{0x1790ull};
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_235<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1790(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x51, 0x91, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x51, 0x91, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = uint256_t{0x179dull};
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_179d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x81, 0x52, 0x80, 0x92, 0x61, 0x60, 0x19, 0x91, 0x61, 0x56}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x81, 0x52, 0x80, 0x92, 0x61, 0x60, 0x19, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s0, s2);
            uint256_t const m0 = s0;
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[1] = uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            top[2] = uint256_t{0x17aeull};
            top[3] = m2;
            top += 3;
            MONAD_AOT_TAIL return b_235<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_17ae(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x01, 0x90, 0x5f}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x01, 0x90, 0x5f}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[-1] = m2;
            top[0] = uint256_t{0x0ull};
            MONAD_AOT_TAIL return b_17b2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_17b2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x81, 0x10, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(s0 < s2);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_17be<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_17ba<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_17ba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top += -4;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_17be(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x90, 0x60, 0x51, 0x61, 0x81, 0x61, 0x56}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x90, 0x60, 0x51, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x20ull};
            top[1] = m0;
            top[2] = t1;
            top[3] = uint256_t{0x17cdull};
            top[4] = t1;
            top += 4;
            MONAD_AOT_TAIL return b_198<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_17cd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x81, 0x52, 0x5f, 0x83, 0x82, 0x01, 0x52, 0x82, 0x82, 0x85, 0x01, 0x01, 0x52, 0x01, 0x61, 0x56}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x81, 0x52, 0x5f, 0x83, 0x82, 0x01, 0x52, 0x82, 0x82, 0x85, 0x01, 0x01, 0x52, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, uint256_t{0x0ull});
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s0 + s2;
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull});
            uint256_t const &s3 = top[-3];
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s3 + s1;
            uint256_t const t3 = t2 + s2;
            aot::mstore<traits>(ctx, gas, t3, s0);
            uint256_t const t4 = s1 + s2;
            top[-2] = t4;
            top += -2;
            MONAD_AOT_TAIL return b_17b2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_17e1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x51, 0x82, 0x10, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x51, 0x82, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::from_bool(s1 < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x10ce); }
            MONAD_AOT_TAIL return b_17eb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_17eb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x91, 0x60, 0x1b, 0x01, 0x01, 0x90, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x91, 0x60, 0x1b, 0x01, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shl_c<5>(s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = t1 + s0;
            uint256_t const t3 = t2 + uint256_t{0x20ull};
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t3;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_17f5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x60, 0x80, 0x83, 0x51, 0x92, 0x83, 0x81, 0x52, 0x01, 0x92, 0x01, 0x90, 0x5f}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x60, 0x80, 0x83, 0x51, 0x92, 0x83, 0x81, 0x52, 0x01, 0x92, 0x01, 0x90, 0x5f}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, t1);
            uint256_t const t2 = s1 + uint256_t{0x20ull};
            uint256_t const t3 = s0 + uint256_t{0x20ull};
            top[-1] = t2;
            top[0] = t3;
            top[1] = t1;
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_1805<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1805(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x81, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s0 < s1);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1812<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_180d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_180d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x90, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint64_t const jt = aot::jump_offset(s4);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-4] = m3;
            top += -4;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1812(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x91, 0x92, 0x60, 0x60, 0x82, 0x61, 0x60, 0x94, 0x88, 0x51, 0x60, 0x80, 0x91, 0x60, 0x80, 0x60, 0x1b, 0x03, 0x81, 0x51, 0x16, 0x84, 0x52, 0x01, 0x51, 0x91, 0x01, 0x52, 0x56}, 4, 11));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1013)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x91, 0x92, 0x60, 0x60, 0x82, 0x61, 0x60, 0x94, 0x88, 0x51, 0x60, 0x80, 0x91, 0x60, 0x80, 0x60, 0x1b, 0x03, 0x81, 0x51, 0x16, 0x84, 0x52, 0x01, 0x51, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = t2 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, t3);
            uint256_t const t4 = t1 + uint256_t{0x20ull};
            uint256_t const t5 = aot::mload<traits>(ctx, gas, t4);
            uint256_t const t6 = s3 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t6, t5);
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m3 = s3;
            top[-3] = m2;
            top[-2] = m1;
            top[-1] = m0;
            top[0] = uint256_t{0x1ull};
            top[1] = uint256_t{0x20ull};
            top[2] = uint256_t{0x40ull};
            top[3] = m3;
            top += 3;
            MONAD_AOT_TAIL return b_1839<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1839(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x01, 0x94, 0x01, 0x92, 0x91, 0x01, 0x61, 0x56}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x01, 0x94, 0x01, 0x92, 0x91, 0x01, 0x61, 0x56}) + 0;
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
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-6] = t1;
            top[-5] = t2;
            top[-4] = m5;
            top[-3] = t3;
            top += -3;
            MONAD_AOT_TAIL return b_1805<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1844(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x94, 0x91, 0x96, 0x95, 0x93, 0x90, 0x96, 0x60, 0x86, 0x52, 0x61, 0x86, 0x01, 0x97, 0x80, 0x51, 0x98, 0x60, 0x60, 0x89, 0x01, 0x52, 0x89, 0x51, 0x80, 0x91, 0x52, 0x60, 0x61, 0x89, 0x01, 0x9a, 0x01, 0x90, 0x5f}, 8, 5));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x94, 0x91, 0x96, 0x95, 0x93, 0x90, 0x96, 0x60, 0x86, 0x52, 0x61, 0x86, 0x01, 0x97, 0x80, 0x51, 0x98, 0x60, 0x60, 0x89, 0x01, 0x52, 0x89, 0x51, 0x80, 0x91, 0x52, 0x60, 0x61, 0x89, 0x01, 0x9a, 0x01, 0x90, 0x5f}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, uint256_t{0xc0ull});
            uint256_t const t1 = s0 + uint256_t{0x120ull};
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const t3 = s0 + uint256_t{0xc0ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0x60ull});
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t2);
            aot::mstore<traits>(ctx, gas, t1, t4);
            uint256_t const t5 = s0 + uint256_t{0x140ull};
            uint256_t const t6 = t2 + uint256_t{0x20ull};
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const m0 = s0;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const m1 = s1;
            top[-7] = t5;
            top[-6] = m7;
            top[-5] = m0;
            top[-4] = m6;
            top[-2] = m5;
            top[-1] = m4;
            top[0] = m2;
            top[1] = m1;
            top[2] = t6;
            top[3] = t4;
            top[4] = uint256_t{0x0ull};
            top += 4;
            MONAD_AOT_TAIL return b_1870<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1870(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x81, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s0 < s1);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_18e0<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1878<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1878(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x61, 0x61, 0x98, 0x99, 0x61, 0x96, 0x95, 0x94, 0x93, 0x60, 0x84, 0x60, 0x61, 0x96, 0x01, 0x51, 0x60, 0x8d, 0x01, 0x52, 0x01, 0x51, 0x61, 0x8b, 0x01, 0x52, 0x89, 0x82, 0x03, 0x60, 0x8b, 0x01, 0x52, 0x61, 0x56}, 12, 5));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x61, 0x61, 0x98, 0x99, 0x61, 0x96, 0x95, 0x94, 0x93, 0x60, 0x84, 0x60, 0x61, 0x96, 0x01, 0x51, 0x60, 0x8d, 0x01, 0x52, 0x01, 0x51, 0x61, 0x8b, 0x01, 0x52, 0x89, 0x82, 0x03, 0x60, 0x8b, 0x01, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x20ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s9 = top[-9];
            uint256_t const t3 = s9 + uint256_t{0xe0ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = s3 + uint256_t{0x40ull};
            uint256_t const t5 = aot::mload<traits>(ctx, gas, t4);
            uint256_t const t6 = s9 + uint256_t{0x100ull};
            aot::mstore<traits>(ctx, gas, t6, t5);
            uint256_t const &s11 = top[-11];
            uint256_t const t7 = s11 - s9;
            uint256_t const t8 = s9 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t8, t7);
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const m11 = s11;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-11] = m10;
            top[-10] = uint256_t{0x3e1ull};
            top[-7] = uint256_t{0x18d2ull};
            top[-6] = m7;
            top[-5] = m6;
            top[-4] = m5;
            top[-3] = uint256_t{0x18c0ull};
            top[-2] = uint256_t{0x18aeull};
            top[-1] = m11;
            top[0] = m4;
            MONAD_AOT_TAIL return b_17f5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_18ae(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x90, 0x94, 0x16, 0x60, 0x88, 0x01, 0x52, 0x56}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x90, 0x94, 0x16, 0x60, 0x88, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s4 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const &s7 = top[-7];
            uint256_t const t2 = s7 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t2, t1);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-4] = m0;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_18c0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x86, 0x01, 0x52, 0x84, 0x82, 0x03, 0x60, 0x86, 0x01, 0x52, 0x61, 0x56}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x86, 0x01, 0x52, 0x84, 0x82, 0x03, 0x60, 0x86, 0x01, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = s5 + uint256_t{0x60ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s2 - s5;
            uint256_t const t3 = s5 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            top += -1;
            MONAD_AOT_TAIL return b_3e4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_18d2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x60, 0x81, 0x84, 0x03, 0x91, 0x01, 0x52, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x60, 0x81, 0x84, 0x03, 0x91, 0x01, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s0 - s2;
            uint256_t const t2 = s2 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t2, t1);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top += -1;
            MONAD_AOT_TAIL return b_3e4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_18e0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x51, 0x80, 0x51, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x8d, 0x52, 0x60, 0x90, 0x81, 0x01, 0x51, 0x81, 0x8e, 0x01, 0x52, 0x60, 0x90, 0x9c, 0x01, 0x9b, 0x90, 0x92, 0x01, 0x91, 0x60, 0x01, 0x61, 0x56}, 12, 5));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x51, 0x80, 0x51, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x16, 0x8d, 0x52, 0x60, 0x90, 0x81, 0x01, 0x51, 0x81, 0x8e, 0x01, 0x52, 0x60, 0x90, 0x9c, 0x01, 0x9b, 0x90, 0x92, 0x01, 0x91, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t2;
            uint256_t const &s11 = top[-11];
            aot::mstore<traits>(ctx, gas, s11, t3);
            uint256_t const t4 = uint256_t{0x20ull} + t1;
            uint256_t const t5 = aot::mload<traits>(ctx, gas, t4);
            uint256_t const t6 = s11 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t6, t5);
            uint256_t const t7 = s11 + uint256_t{0x40ull};
            uint256_t const t8 = s2 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            uint256_t const t9 = uint256_t{0x1ull} + s0;
            top[-11] = t7;
            top[-2] = t8;
            top[0] = t9;
            MONAD_AOT_TAIL return b_1870<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1919(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1962(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_1cbb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1978(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_19c5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x93, 0x90, 0x92, 0x91, 0x60, 0x81, 0x51, 0x91, 0x01, 0x20, 0x93, 0x61, 0x83, 0x51, 0x61, 0x56}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x93, 0x90, 0x92, 0x91, 0x60, 0x81, 0x51, 0x91, 0x01, 0x20, 0x93, 0x61, 0x83, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const t2 = s2 + uint256_t{0x20ull};
            auto const h10 = aot::sha3_any<traits>(ctx, gas, t2, t1);
            gas = ctx->gas_remaining;
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const m3 = s3;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-4] = h10;
            top[-3] = m1;
            top[-2] = m3;
            top[-1] = m4;
            top[1] = uint256_t{0x19dbull};
            top[2] = t3;
            top += 2;
            MONAD_AOT_TAIL return b_1d64<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_19db(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x94, 0x5f}, 6, 1));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x94, 0x5f}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-5] = m0;
            top[0] = m5;
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_19de<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_19de(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x51, 0x81, 0x10, 0x15, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x51, 0x81, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s4);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::from_bool(s0 < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return b_1ab4<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_19e8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_19e8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x61, 0x61, 0x60, 0x93, 0x88, 0x61, 0x56}, 5, 6));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x61, 0x61, 0x60, 0x93, 0x88, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[0] = uint256_t{0x1ull};
            top[1] = m0;
            top[2] = uint256_t{0x19f7ull};
            top[3] = uint256_t{0xfbdull};
            top[4] = m0;
            top[5] = m4;
            top += 5;
            MONAD_AOT_TAIL return b_17e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_19f7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x61, 0x84, 0x8a, 0x61, 0x56}, 7, 6));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x61, 0x84, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[1] = uint256_t{0x1a0eull};
            top[2] = uint256_t{0x20ull};
            top[3] = uint256_t{0x1a06ull};
            top[4] = m1;
            top[5] = m6;
            top += 5;
            MONAD_AOT_TAIL return b_17e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a06(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x01, 0x51, 0x15, 0x15, 0x90, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x01, 0x51, 0x15, 0x15, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 + s1;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t5;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a0e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x61, 0x85, 0x8b, 0x61, 0x56}, 8, 6));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x61, 0x85, 0x8b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[1] = uint256_t{0x1aa0ull};
            top[2] = uint256_t{0x40ull};
            top[3] = uint256_t{0x1a1dull};
            top[4] = m2;
            top[5] = m7;
            top += 5;
            MONAD_AOT_TAIL return b_17e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a1d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x01, 0x51, 0x91, 0x61, 0x60, 0x61, 0x87, 0x8d, 0x61, 0x56}, 11, 5));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x01, 0x51, 0x91, 0x61, 0x60, 0x61, 0x87, 0x8d, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 + s1;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[-3] = t3;
            top[-1] = m3;
            top[0] = uint256_t{0x1a92ull};
            top[1] = uint256_t{0x60ull};
            top[2] = uint256_t{0x1a30ull};
            top[3] = m5;
            top[4] = m10;
            top += 4;
            MONAD_AOT_TAIL return b_17e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a30(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x01, 0x51, 0x60, 0x81, 0x51, 0x91, 0x01, 0x20, 0x60, 0x51, 0x94, 0x85, 0x93, 0x60, 0x85, 0x01, 0x97, 0x88, 0x90, 0x94, 0x93, 0x92, 0x60, 0x92, 0x60, 0x83, 0x01, 0x96, 0x7f, 0x84, 0x52, 0x60, 0x80, 0x60, 0x1b, 0x03, 0x16, 0x60, 0x84, 0x01, 0x52, 0x15, 0x15, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x01, 0x52, 0x56}, 7, 8));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x01, 0x51, 0x60, 0x81, 0x51, 0x91, 0x01, 0x20, 0x60, 0x51, 0x94, 0x85, 0x93, 0x60, 0x85, 0x01, 0x97, 0x88, 0x90, 0x94, 0x93, 0x92, 0x60, 0x92, 0x60, 0x83, 0x01, 0x96, 0x7f, 0x84, 0x52, 0x60, 0x80, 0x60, 0x1b, 0x03, 0x16, 0x60, 0x84, 0x01, 0x52, 0x15, 0x15, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 + s1;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const t5 = t3 + uint256_t{0x20ull};
            auto const h9 = aot::sha3_any<traits>(ctx, gas, t5, t4);
            gas = ctx->gas_remaining;
            uint256_t const t6 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t7 = t6 + uint256_t{0x20ull};
            uint256_t const t8 = t7 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t7, uint256_t{0x76dfe9729e8a6cdeull, 0xed4d377e86270174ull, 0x885a8c0afe16fa80ull, 0xfd3926a097b5d365ull});
            uint256_t const &s6 = top[-6];
            uint256_t const t9 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s6;
            uint256_t const t10 = t7 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t10, t9);
            uint256_t const &s3 = top[-3];
            uint256_t const t11 = aot::from_bool(!aot::nonzero(s3));
            uint256_t const t12 = aot::from_bool(!aot::nonzero(t11));
            uint256_t const t13 = t7 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t13, t12);
            uint256_t const t14 = t7 + uint256_t{0x60ull};
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, t14, s5);
            uint256_t const t15 = t7 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t15, h9);
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-6] = t7;
            top[-5] = t6;
            top[-3] = t6;
            top[-2] = t8;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a92(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x03, 0x60, 0x19, 0x81, 0x01, 0x83, 0x52, 0x82, 0x61, 0x56}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x03, 0x60, 0x19, 0x81, 0x01, 0x83, 0x52, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const t2 = t1 + uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, t2);
            uint256_t const m3 = s3;
            top[-1] = t1;
            top[0] = m3;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1aa0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x90, 0x20, 0x61, 0x82, 0x8a, 0x61, 0x56}, 10, 3));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x90, 0x20, 0x61, 0x82, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            auto const h3 = aot::sha3_any<traits>(ctx, gas, s1, t1);
            gas = ctx->gas_remaining;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[-1] = h3;
            top[0] = uint256_t{0x1aadull};
            top[1] = m2;
            top[2] = m9;
            top += 2;
            MONAD_AOT_TAIL return b_17e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1aad(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x52, 0x01, 0x61, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x52, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s0, s1);
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s2 + s3;
            top[-3] = t1;
            top += -3;
            MONAD_AOT_TAIL return b_19de<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ab4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x92, 0x50, 0x92, 0x61, 0x61, 0x92, 0x95, 0x60, 0x51, 0x61, 0x81, 0x61, 0x60, 0x82, 0x01, 0x80, 0x95, 0x61, 0x56}, 7, 7));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x92, 0x50, 0x92, 0x61, 0x61, 0x92, 0x95, 0x60, 0x51, 0x61, 0x81, 0x61, 0x60, 0x82, 0x01, 0x80, 0x95, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-6] = m3;
            top[-5] = m2;
            top[-4] = m1;
            top[-3] = uint256_t{0x1b3full};
            top[-2] = m5;
            top[-1] = uint256_t{0x1a92ull};
            top[0] = t2;
            top[1] = t1;
            top[2] = uint256_t{0x1ad5ull};
            top[3] = t1;
            top[4] = uint256_t{0x1a92ull};
            top[5] = t2;
            top[6] = m6;
            top += 6;
            MONAD_AOT_TAIL return b_1d96<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ad5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x90, 0x20, 0x60, 0x80, 0x51, 0x7f, 0x60, 0x82, 0x01, 0x90, 0x81, 0x52, 0x33, 0x92, 0x82, 0x01, 0x92, 0x90, 0x92, 0x52, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x97, 0x88, 0x16, 0x60, 0x82, 0x01, 0x52, 0x93, 0x90, 0x96, 0x16, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x94, 0x90, 0x94, 0x52, 0x60, 0x82, 0x01, 0x93, 0x90, 0x93, 0x52, 0x91, 0x82, 0x90, 0x60, 0x82, 0x01, 0x90, 0x56}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x90, 0x20, 0x60, 0x80, 0x51, 0x7f, 0x60, 0x82, 0x01, 0x90, 0x81, 0x52, 0x33, 0x92, 0x82, 0x01, 0x92, 0x90, 0x92, 0x52, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x97, 0x88, 0x16, 0x60, 0x82, 0x01, 0x52, 0x93, 0x90, 0x96, 0x16, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x94, 0x90, 0x94, 0x52, 0x60, 0x82, 0x01, 0x93, 0x90, 0x93, 0x52, 0x91, 0x82, 0x90, 0x60, 0x82, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            auto const h3 = aot::sha3_any<traits>(ctx, gas, s1, t1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t3 = t2 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0xbeff8ea5168af917ull, 0xee6e910560d8f8eeull, 0x48d71d25db5eb5a6ull, 0x4b21a98ca11613e8ull});
            uint256_t const t4 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t5 = t2 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const &s6 = top[-6];
            uint256_t const t6 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s6;
            uint256_t const t7 = t2 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t7, t6);
            uint256_t const &s3 = top[-3];
            uint256_t const t8 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s3;
            uint256_t const t9 = t2 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t9, t8);
            uint256_t const t10 = t2 + uint256_t{0xa0ull};
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, t10, s5);
            uint256_t const t11 = t2 + uint256_t{0xc0ull};
            aot::mstore<traits>(ctx, gas, t11, h3);
            uint256_t const t12 = t2 + uint256_t{0xe0ull};
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-6] = t3;
            top[-5] = t2;
            top[-3] = t2;
            top[-2] = t12;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1b3f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x90, 0x20, 0x90, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x90, 0x20, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            auto const h3 = aot::sha3_any<traits>(ctx, gas, s1, t1);
            gas = ctx->gas_remaining;
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = h3;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1b45(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x63, 0x60, 0x1b, 0x60, 0x82, 0x01, 0x52, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x92, 0x83, 0x16, 0x60, 0x82, 0x01, 0x52, 0x92, 0x90, 0x91, 0x16, 0x60, 0x83, 0x01, 0x52, 0x60, 0x80, 0x83, 0x01, 0x93, 0x90, 0x93, 0x52, 0x91, 0x81, 0x52, 0x61, 0x91, 0x61, 0x60, 0x83, 0x61, 0x56}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x63, 0x60, 0x1b, 0x60, 0x82, 0x01, 0x52, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x92, 0x83, 0x16, 0x60, 0x82, 0x01, 0x52, 0x92, 0x90, 0x91, 0x16, 0x60, 0x83, 0x01, 0x52, 0x60, 0x80, 0x83, 0x01, 0x93, 0x90, 0x93, 0x52, 0x91, 0x81, 0x52, 0x61, 0x91, 0x61, 0x60, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x23b872dd00000000ull});
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s1;
            uint256_t const t4 = t1 + uint256_t{0x24ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const &s2 = top[-2];
            uint256_t const t5 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s2;
            uint256_t const t6 = t1 + uint256_t{0x44ull};
            aot::mstore<traits>(ctx, gas, t6, t5);
            uint256_t const t7 = t1 + uint256_t{0x64ull};
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, t7, s3);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x64ull});
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-3] = uint256_t{0x130ull};
            top[-2] = t1;
            top[-1] = m0;
            top[0] = uint256_t{0x1962ull};
            top[1] = uint256_t{0x84ull};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ba7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x63, 0x60, 0x1b, 0x81, 0x52, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x87, 0x81, 0x16, 0x60, 0x83, 0x01, 0x52, 0x86, 0x16, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x89, 0x90, 0x52, 0x60, 0x81, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x91, 0x90, 0x91, 0x16, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x92, 0x90, 0x92, 0x52, 0x60, 0x82, 0x01, 0x52, 0x5f, 0x81, 0x60, 0x81, 0x83, 0x88, 0x5a, 0xf1, 0x90, 0x81, 0x61, 0x57}, 8, 5));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x63, 0x60, 0x1b, 0x81, 0x52, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x87, 0x81, 0x16, 0x60, 0x83, 0x01, 0x52, 0x86, 0x16, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x89, 0x90, 0x52, 0x60, 0x81, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x91, 0x90, 0x91, 0x16, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x92, 0x90, 0x92, 0x52, 0x60, 0x82, 0x01, 0x52, 0x5f, 0x81, 0x60, 0x81, 0x83, 0x88, 0x5a, 0xf1, 0x90, 0x81, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xd505accf00000000ull});
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s5;
            uint256_t const t3 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const &s4 = top[-4];
            uint256_t const t4 = s4 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t5 = t1 + uint256_t{0x24ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const t6 = t1 + uint256_t{0x44ull};
            uint256_t const &s7 = top[-7];
            aot::mstore<traits>(ctx, gas, t6, s7);
            uint256_t const t7 = t1 + uint256_t{0x64ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t7, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t8 = uint256_t{0xffull} & s1;
            uint256_t const t9 = t1 + uint256_t{0x84ull};
            aot::mstore<traits>(ctx, gas, t9, t8);
            uint256_t const t10 = t1 + uint256_t{0xa4ull};
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, t10, s3);
            uint256_t const t11 = t1 + uint256_t{0xc4ull};
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t11, s2);
            uint256_t const t12 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xf1, 0x90, 0x81, 0x61, 0x57}) + 0))};
            uint256_t const &s6 = top[-6];
            auto const c65 = aot::call<traits>(ctx, gas, t12, s6, uint256_t{0x0ull}, t1, uint256_t{0xe4ull}, t1, uint256_t{0x0ull}, (aot::gas_of<traits>({0x90, 0x81, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            bool const j69 = aot::nonzero(c65);
            top[-3] = c65;
            top[-2] = t1;
            top += -2;
            if (j69) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1ca7); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1c01);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c07(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x63, 0x60, 0x1b, 0x81, 0x52, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x92, 0x83, 0x16, 0x60, 0x82, 0x01, 0x52, 0x91, 0x16, 0x60, 0x82, 0x01, 0x52, 0x90, 0x60, 0x90, 0x82, 0x90, 0x60, 0x90, 0x82, 0x90, 0x5a, 0xfa, 0x90, 0x81, 0x15, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x63, 0x60, 0x1b, 0x81, 0x52, 0x60, 0x60, 0x60, 0x1b, 0x03, 0x92, 0x83, 0x16, 0x60, 0x82, 0x01, 0x52, 0x91, 0x16, 0x60, 0x82, 0x01, 0x52, 0x90, 0x60, 0x90, 0x82, 0x90, 0x60, 0x90, 0x82, 0x90, 0x5a, 0xfa, 0x90, 0x81, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdd62ed3e00000000ull});
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s1;
            uint256_t const t3 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const &s0 = top[0];
            uint256_t const t4 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s0;
            uint256_t const t5 = t1 + uint256_t{0x24ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const t6 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x90, 0x81, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const &s2 = top[-2];
            uint256_t const k35_3 = uint256_t{0x44ull};
            uint256_t const k35_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r35;
            runtime::staticcall<traits>(ctx, &r35, &t6, &s2, &t1, &k35_3, &t1, &k35_5, (aot::gas_of<traits>({0x90, 0x81, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t7 = aot::from_bool(!aot::nonzero(r35));
            bool const j40 = aot::nonzero(t7);
            top[-2] = r35;
            top[-1] = t1;
            top += -1;
            if (j40) { MONAD_AOT_TAIL return b_7af<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1c3f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c3f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x91, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x91, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            bool const j3 = aot::nonzero(s1);
            top[-1] = uint256_t{0x0ull};
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1c82); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1c45);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c4d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x62, 0x60, 0x1b, 0x81, 0x52, 0x60, 0x60, 0x82, 0x01, 0x52, 0x60, 0x60, 0x82, 0x01, 0x52, 0x6d, 0x60, 0x1b, 0x60, 0x82, 0x01, 0x52, 0x60, 0x90, 0xfd}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x62, 0x60, 0x1b, 0x81, 0x52, 0x60, 0x60, 0x82, 0x01, 0x52, 0x60, 0x60, 0x82, 0x01, 0x52, 0x6d, 0x60, 0x1b, 0x60, 0x82, 0x01, 0x52, 0x60, 0x90, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8c379a000000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x20ull});
            uint256_t const t3 = t1 + uint256_t{0x24ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0xeull});
            uint256_t const t4 = t1 + uint256_t{0x44ull};
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x0ull, 0x0ull, 0x61696c7572650000ull, 0x5065726d69742066ull});
            aot::finish(ctx, gas, StatusCode::Revert, t1, uint256_t{0x64ull});
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c92(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x81, 0x83, 0x61, 0x56}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x81, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0x799ull};
            top[2] = m0;
            top[3] = m1;
            top += 3;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1cbb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x80, 0x61, 0x92, 0x60, 0x80, 0x60, 0x1b, 0x03, 0x16, 0x93, 0x60, 0x81, 0x51, 0x91, 0x01, 0x82, 0x86, 0x5a, 0xf1, 0x3d, 0x15, 0x61, 0x57}, 2, 7));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x80, 0x61, 0x92, 0x60, 0x80, 0x60, 0x1b, 0x03, 0x16, 0x93, 0x60, 0x81, 0x51, 0x91, 0x01, 0x82, 0x86, 0x5a, 0xf1, 0x3d, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s0;
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const t3 = s1 + uint256_t{0x20ull};
            uint256_t const t4 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xf1, 0x3d, 0x15, 0x61, 0x57}) + 0))};
            auto const c20 = aot::call<traits>(ctx, gas, t4, t1, uint256_t{0x0ull}, t3, t2, uint256_t{0x0ull}, uint256_t{0x0ull}, (aot::gas_of<traits>({0x3d, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j24 = aot::nonzero(t6);
            top[-1] = t1;
            top[0] = uint256_t{0x1d03ull};
            top[1] = c20;
            top += 1;
            if (j24) { MONAD_AOT_TAIL return b_1d5c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1cdb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1cdb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x1ce5ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_375<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ce5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x61, 0x60, 0x51, 0x93, 0x84, 0x61, 0x56}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x61, 0x60, 0x51, 0x93, 0x84, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = t1;
            top[0] = m2;
            top[1] = uint256_t{0x1cf3ull};
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1cf3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x52, 0x3d, 0x5f, 0x60, 0x84, 0x01, 0x3e}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x52, 0x3d, 0x5f, 0x60, 0x84, 0x01, 0x3e}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s2, s0);
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t2 = s2 + uint256_t{0x20ull};
            uint256_t const k8_1 = uint256_t{0x0ull};
            ctx->gas_remaining = gas;
            runtime::returndatacopy<traits>(ctx, &t2, &k8_1, &t1);
            gas = ctx->gas_remaining;
            top += -1;
            MONAD_AOT_TAIL return b_1cfd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1cfd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x61, 0x56}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[1] = m3;
            top += 1;
            MONAD_AOT_TAIL return b_1dc3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d03(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x51, 0x80, 0x15, 0x15, 0x91, 0x82, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x51, 0x80, 0x15, 0x15, 0x91, 0x82, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j9 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[0] = t3;
            top[1] = t1;
            top[2] = m0;
            top += 2;
            if (j9) { MONAD_AOT_TAIL return b_1d33<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1d0f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d0f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            bool const j4 = aot::nonzero(s2);
            top += -3;
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1d18); }
            MONAD_AOT_TAIL return b_1d16<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d16(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d33(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x81, 0x01, 0x93, 0x50, 0x91, 0x81, 0x01, 0x03, 0x12, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x81, 0x01, 0x93, 0x50, 0x91, 0x81, 0x01, 0x03, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x20ull} + s0;
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s0 + s1;
            uint256_t const t3 = t2 - s0;
            uint256_t const t4 = aot::from_bool(slt(t3, uint256_t{0x20ull}));
            bool const j13 = aot::nonzero(t4);
            top[-2] = t1;
            top += -2;
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f); }
            MONAD_AOT_TAIL return b_1d44<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d44(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x51, 0x61, 0x81, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x51, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            top[0] = uint256_t{0x1d55ull};
            top[1] = t1;
            top[2] = uint256_t{0x1d51ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_be0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d51(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x90, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top[-1] = t1;
            top += -1;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d55(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x80, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_1d0f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d5c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x90, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x60ull};
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_1cfd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d64(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x61, 0x82, 0x61, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = m0;
            top[0] = m1;
            top[1] = uint256_t{0x1d6eull};
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_235<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d6e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x51, 0x91, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x51, 0x91, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = uint256_t{0x1d7bull};
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_205<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d7b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x81, 0x52, 0x80, 0x92, 0x61, 0x60, 0x19, 0x91, 0x61, 0x56}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x81, 0x52, 0x80, 0x92, 0x61, 0x60, 0x19, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s0, s2);
            uint256_t const m0 = s0;
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[1] = uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            top[2] = uint256_t{0x1d8cull};
            top[3] = m2;
            top += 3;
            MONAD_AOT_TAIL return b_235<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d8c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x01, 0x90, 0x60, 0x36, 0x91, 0x01, 0x37, 0x56}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x01, 0x90, 0x60, 0x36, 0x91, 0x01, 0x37, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = s2 + uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t3, &t2, &t1);
            gas = ctx->gas_remaining;
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top += -4;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d96(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x51, 0x60, 0x90, 0x91, 0x01, 0x90, 0x5f}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x51, 0x60, 0x90, 0x91, 0x01, 0x90, 0x5f}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = s0 + uint256_t{0x20ull};
            top[0] = t2;
            top[1] = t1;
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_1da0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1da0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x81, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s0 < s1);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1dad<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1da8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1da8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x90, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint64_t const jt = aot::jump_offset(s4);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-4] = m3;
            top += -4;
            if (MONAD_LIKELY(jt < 7746)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1dad(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x51, 0x84, 0x52, 0x60, 0x93, 0x84, 0x01, 0x93, 0x90, 0x92, 0x01, 0x91, 0x60, 0x01, 0x61, 0x56}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x51, 0x84, 0x52, 0x60, 0x93, 0x84, 0x01, 0x93, 0x90, 0x92, 0x01, 0x91, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, t1);
            uint256_t const t2 = uint256_t{0x20ull} + s3;
            uint256_t const t3 = s2 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            uint256_t const t4 = uint256_t{0x1ull} + s0;
            top[-3] = t2;
            top[-2] = t3;
            top[0] = t4;
            MONAD_AOT_TAIL return b_1da0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1dc3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x61, 0x57}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            bool const j3 = aot::nonzero(s1);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_1de7<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1dc9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dc9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x80, 0x51, 0x15, 0x61, 0x57}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x80, 0x51, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j5 = aot::nonzero(t2);
            top += -1;
            if (j5) { MONAD_AOT_TAIL return b_1dd8<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1dd1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dd1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x51, 0x90, 0x60, 0x01, 0xfd}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x51, 0x90, 0x60, 0x01, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = uint256_t{0x20ull} + s0;
            aot::finish(ctx, gas, StatusCode::Revert, t2, t1);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1dd8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x60, 0x1b, 0x5f, 0x52, 0x60, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x60, 0x1b, 0x5f, 0x52, 0x60, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x1425ea4200000000ull});
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x4ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1de7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x51, 0x15, 0x80, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x51, 0x15, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j6 = aot::nonzero(t2);
            top[1] = t2;
            top += 1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1e18); }
            MONAD_AOT_TAIL return b_1df0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1df0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j2 = aot::nonzero(s0);
            top += -1;
            if (j2) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1df8); }
            MONAD_AOT_TAIL return b_1df5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1df5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x90, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-2] = m1;
            top += -2;
            if (MONAD_LIKELY(jt < 7746)) {
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

    template void c_a3b36a6aa3c2fb58::run<EvmTraits<MONAD_ETH_OSAKA>>(
        void *, Context *, interpreter::Intercode const *, uint256_t *, void *);
}
