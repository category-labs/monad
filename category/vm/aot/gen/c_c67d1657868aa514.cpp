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

// Written by aotgen.py from the code whose keccak is c67d1657868aa5146eaf24fb879fb1fdec3d2d493b3683a61c9c2f4fb2851131: not to be edited.

#include <category/vm/aot/ops.hpp>
#include <category/vm/interpreter/execute.hpp>
#include <category/vm/interpreter/intercode.hpp>

#define MONAD_AOT_TAIL __attribute__((musttail))

namespace monad::vm::aot
{
    using runtime::Context;
    using runtime::StatusCode;

    // 9152 bytes, keccak c67d1657868aa5146eaf24fb879fb1fdec3d2d493b3683a61c9c2f4fb2851131
    namespace c_c67d1657868aa514
    {
        template <Traits traits>
        using Block = void (*)(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        [[gnu::noinline]] void b_0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_15(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_29(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_34(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_55(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_60(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_76(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_81(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_8c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_97(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ad(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_cc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_108(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_114(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_12b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_133(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_13f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_14b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_159(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_164(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_173(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_222(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_25b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_26b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_26e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_276(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_294(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2a0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2e1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2ed(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2f6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2f9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_30b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_311(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_31b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_321(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_342(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_36c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_37f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_396(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3b9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3df(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3f9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4ab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4d7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4e9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_501(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_515(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_5ca(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_5f4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_67a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_681(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6ab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_6b2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_6bb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_6c4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6db(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_77f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_783(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_7a4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_7b4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_7de(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_806(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_84d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_85a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_946(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_96f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9b0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9d9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a28(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a2f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a59(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a60(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a68(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a70(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a92(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_aa4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_acd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ade(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ae7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b12(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_b1a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b45(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_b4c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b60(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_b6f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_b7c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_bd1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_bde(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_be6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c11(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c18(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c44(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c51(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c57(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_c62(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c85(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c93(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_cab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_cbb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ccf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_cf2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_cfe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d09(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d23(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d70(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d78(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d7e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_db7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_dbf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_dec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_df3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e0c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e17(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e28(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e35(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e43(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_e50(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_e5d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e77(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_e7a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e82(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_e93(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_eaf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ebb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ec6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ed6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ed9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ee1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f02(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f64(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f6d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f75(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f78(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f8b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f91(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f97(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fac(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fb2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fe9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ff4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1002(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_100b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1018(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1027(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1037(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1075(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_107d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10a8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_10b0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10db(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_10e2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10f9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1105(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1113(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1125(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1134(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_11e3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_121c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_122a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1274(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_129f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12b2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12bd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12c7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12d9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12e2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1318(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1398(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_13b0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_13e3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_13fb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_13ff(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1417(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_141b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1433(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1437(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1474(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1478(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_149a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_14a0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14c2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_14c3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14e5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_14e6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1508(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1509(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1529(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_152a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1556(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1563(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_156c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1584(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_15a6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_15c1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_15ce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_15e0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_15ee(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_15ef(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_15ff(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1607(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1619(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_161a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1627(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1639(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_164a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_164b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1659(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1666(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_167c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1689(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1693(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_16a0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_16ba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_16c6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_16ce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_16e3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_16f4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1706(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1714(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_175e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1768(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_17a1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_17f6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1802(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1810(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1812(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_181f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_184f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_18b5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_190d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_196c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1976(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_197c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_199b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_199d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a0c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a42(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a60(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ace(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ad3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1b1e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b46(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1bd3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1bd9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1be1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1c25(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c3a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c48(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1c60(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1c65(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c8d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1cf7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d0e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d16(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d2e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d31(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d39(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d42(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d4d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d5a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d69(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d78(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d84(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1dad(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1db3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1e47(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e90(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ebb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ec5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ed2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f00(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f0a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f32(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f66(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f71(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f79(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f7f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f93(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f9a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fa2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1fab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1fbe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_204c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2054(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_20b1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_20be(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_20c7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_20d0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_20d9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_20e4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_20f0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2102(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2124(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2145(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_214b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21b5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21f5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_222e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_22ce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_22d4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_22ff(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_232a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2337(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2344(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_234d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2378(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        void bad(Context *const ctx, uint256_t const *, uint256_t *, int64_t)
        {
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        inline constexpr Block<traits> jump_table[9152] = {
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_15<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_c6<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_114<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_12b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_133<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_14b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_164<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_173<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_222<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_25b<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_26b<traits>, &bad<traits>, &bad<traits>, &b_26e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_294<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2e1<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2ed<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2f6<traits>, &bad<traits>, &bad<traits>, &b_2f9<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_30b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_311<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_31b<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_321<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3f9<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_515<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_67a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_6b2<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_6bb<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_6c4<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_783<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_7a4<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, &bad<traits>, &b_a28<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_a60<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_a68<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_a70<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_ade<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_b1a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_b4c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_b6f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_b7c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_bd1<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_bde<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_c18<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_c51<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_c62<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_cfe<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_d70<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_d78<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_d7e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_db7<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_df3<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_e50<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_e5d<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_e7a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_e93<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_ebb<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_ed6<traits>, &bad<traits>, &bad<traits>, &b_ed9<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_f02<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_f64<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_f6d<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_f78<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_f8b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_f91<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_f97<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_fac<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_fb2<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &b_fe9<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1002<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_100b<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1018<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1027<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1037<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1075<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_10b0<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_10e2<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1105<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1125<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1134<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_11e3<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_121c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_122a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1398<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &b_13e3<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_13ff<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_141b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1437<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1478<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_14a0<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_14c3<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_14e6<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1509<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_152a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1563<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_15c1<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_15ef<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1607<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_161a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_164b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1666<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1693<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_16a0<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_16c6<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_16e3<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1714<traits>, &bad<traits>,
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
            &b_175e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &b_17a1<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1802<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1810<traits>, &bad<traits>,
            &b_1812<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_184f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &b_18b5<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_196c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_197c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_199d<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1a60<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1ace<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1ad3<traits>, &bad<traits>, &bad<traits>,
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
            &b_1b1e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1bd3<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1bd9<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1be1<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1c25<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1c60<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1c65<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1cf7<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1d2e<traits>, &bad<traits>, &bad<traits>, &b_1d31<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1d42<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1d4d<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1d5a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1d78<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1d84<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1dad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1db3<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1e47<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &b_1ebb<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1ec5<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1ed2<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1f00<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1f0a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1f66<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1f71<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1f7f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1f93<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1f9a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1fab<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1fbe<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2054<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_20b1<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_20c7<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_20e4<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2102<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_222e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_22d4<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &b_232a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2337<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2344<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>,
        };

        template <Traits traits>
        [[gnu::noinline]] void b_0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x81, 0x52, 0x60, 0x90, 0x81, 0x36, 0x10, 0x15, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x81, 0x52, 0x60, 0x90, 0x81, 0x36, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, uint256_t{0x80ull});
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x4ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j11 = aot::nonzero(t3);
            top[1] = uint256_t{0x4ull};
            top[2] = uint256_t{0x40ull};
            top += 2;
            if (j11) { MONAD_AOT_TAIL return b_15<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_11<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_15(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x90, 0x81, 0x35, 0x60, 0x1c, 0x80, 0x63, 0x14, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x90, 0x81, 0x35, 0x60, 0x1c, 0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x0ull});
            uint256_t const t2 = aot::shr_c<224>(t1);
            uint256_t const t3 = aot::from_bool(uint256_t{0xd58b1dbull} == t2);
            bool const j11 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x0ull};
            top[1] = m0;
            top[2] = t2;
            top += 2;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x126c); }
            MONAD_AOT_TAIL return b_29<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_29(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x137c29feull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_1075<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_34<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_34(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x2a2d80d1ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_db7<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x2b67b570ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_bde<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_4a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x30f28b7aull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_ade<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_55<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_55(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x3644e515ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xa9d); }
            MONAD_AOT_TAIL return b_60<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_60(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x36c78516ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_a28<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_6b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x3ff9dcb1ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x9a8); }
            MONAD_AOT_TAIL return b_76<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_76(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x4fe02b44ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x93f); }
            MONAD_AOT_TAIL return b_81<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_81(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x65d9723cull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x7ac); }
            MONAD_AOT_TAIL return b_8c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_8c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x87517c45ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_67a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_97<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_97(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x927da105ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x5c3); }
            MONAD_AOT_TAIL return b_a2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xcc53287full} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x4a3); }
            MONAD_AOT_TAIL return b_ad<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ad(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xedd9444bull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x33a); }
            MONAD_AOT_TAIL return b_b8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x63, 0x14, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xfe8ec1a7ull} == s0);
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_c6<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_c2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j3 = aot::nonzero(t1);
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x336); }
            MONAD_AOT_TAIL return b_cc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_cc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0xc0ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x336); }
            MONAD_AOT_TAIL return b_f6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x67, 0x83, 0x35, 0x81, 0x81, 0x11, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x67, 0x83, 0x35, 0x81, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::calldataload(ctx, s2);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j7 = aot::nonzero(t2);
            top[1] = uint256_t{0xffffffffffffffffull};
            top[2] = t1;
            top += 2;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x332); }
            MONAD_AOT_TAIL return b_108<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_108(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x86, 0x01, 0x61, 0x56}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x86, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s4 = top[-4];
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s4 + s0;
            top[0] = uint256_t{0x114ull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_164b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_114(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x82, 0x81, 0x11, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::from_bool(s1 < t1);
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x32e); }
            MONAD_AOT_TAIL return b_11f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x87, 0x01, 0x61, 0x56}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x87, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s5 = top[-5];
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s5 + s0;
            top[0] = uint256_t{0x12bull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_161a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_12b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x133ull};
            top += 1;
            MONAD_AOT_TAIL return b_14e6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_133(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x60, 0x35, 0x85, 0x81, 0x11, 0x61, 0x57}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x60, 0x35, 0x85, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = aot::from_bool(s4 < t1);
            bool const j8 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[0] = m2;
            top[1] = t1;
            top += 1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x32a); }
            MONAD_AOT_TAIL return b_13f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_13f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x8a, 0x01, 0x61, 0x56}, 9, 3));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x8a, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s8 = top[-8];
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s8 + s0;
            top[0] = uint256_t{0x14bull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_15c1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_14b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x98, 0x90, 0x95, 0x60, 0x35, 0x90, 0x81, 0x11, 0x61, 0x57}, 10, 2));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x98, 0x90, 0x95, 0x60, 0x35, 0x90, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const &s6 = top[-6];
            uint256_t const t2 = aot::from_bool(s6 < t1);
            bool const j10 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[-9] = m0;
            top[-6] = m1;
            top[-1] = m9;
            top[0] = t1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x326); }
            MONAD_AOT_TAIL return b_159<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_159(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x91, 0x36, 0x91, 0x01, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x91, 0x36, 0x91, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s0 + s1;
            top[-1] = uint256_t{0x164ull};
            top[0] = t1;
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_15c1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_164(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x96, 0x90, 0x95, 0x81, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 8, 4));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x96, 0x90, 0x95, 0x81, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s7);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-7] = m0;
            top[-6] = m1;
            top[-1] = m7;
            top[0] = t1;
            top[1] = m6;
            top[2] = uint256_t{0x173ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_13ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_173(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x7f, 0x83, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x82, 0x51, 0x9a, 0x8b, 0x91, 0x81, 0x61, 0x60, 0x85, 0x01, 0x80, 0x96, 0x61, 0x56}, 11, 7));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x7f, 0x83, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x82, 0x51, 0x9a, 0x8b, 0x91, 0x81, 0x61, 0x60, 0x85, 0x01, 0x80, 0x96, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x6bull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x657246726f6d2854ull, 0x73735472616e7366ull, 0x7463685769746e65ull, 0x5065726d69744261ull});
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s1 + s2;
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x7465642c61646472ull, 0x5d207065726d6974ull, 0x697373696f6e735bull, 0x6f6b656e5065726dull});
            uint256_t const t3 = s1 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0x652c75696e743235ull, 0x323536206e6f6e63ull, 0x6465722c75696e74ull, 0x657373207370656eull});
            uint256_t const t4 = s1 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x0ull, 0x0ull, 0x6e652c0000000000ull, 0x3620646561646c69ull});
            uint256_t const t5 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const t6 = t5 + uint256_t{0x20ull};
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m1 = s1;
            top[-10] = t5;
            top[-1] = t6;
            top[0] = t5;
            top[1] = m10;
            top[2] = m0;
            top[3] = m10;
            top[4] = uint256_t{0x222ull};
            top[5] = t6;
            top[6] = m1;
            top += 6;
            MONAD_AOT_TAIL return b_1f93<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_222(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x82, 0x37, 0x01, 0x8a, 0x81, 0x52, 0x03, 0x99, 0x61, 0x7f, 0x9b, 0x8c, 0x81, 0x01, 0x83, 0x52, 0x82, 0x61, 0x56}, 15, 1));
            if (MONAD_UNLIKELY(top - bottom < 15)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x82, 0x37, 0x01, 0x8a, 0x81, 0x52, 0x03, 0x99, 0x61, 0x7f, 0x9b, 0x8c, 0x81, 0x01, 0x83, 0x52, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const &s1 = top[-1];
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &s0, &s2, &s1);
            gas = ctx->gas_remaining;
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s0 + s3;
            uint256_t const &s13 = top[-13];
            aot::mstore<traits>(ctx, gas, t1, s13);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = t1 - s4;
            uint256_t const t3 = t2 + uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s14 = top[-14];
            aot::mstore<traits>(ctx, gas, s14, t3);
            uint256_t const m14 = s14;
            top[-14] = uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            top[-4] = m14;
            top[-3] = uint256_t{0x25bull};
            top[-2] = t2;
            top[-1] = m14;
            top += -1;
            MONAD_AOT_TAIL return b_1437<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_25b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x90, 0x20, 0x90, 0x85, 0x51, 0x51, 0x61, 0x81, 0x61, 0x56}, 7, 3));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x90, 0x20, 0x90, 0x85, 0x51, 0x51, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            auto const h3 = aot::sha3_any<traits>(ctx, gas, s1, t1);
            gas = ctx->gas_remaining;
            uint256_t const &s6 = top[-6];
            uint256_t const t2 = aot::mload<traits>(ctx, gas, s6);
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = h3;
            top[-1] = m2;
            top[0] = t3;
            top[1] = uint256_t{0x26bull};
            top[2] = t3;
            top += 2;
            MONAD_AOT_TAIL return b_1ebb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_26b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x8a}, 11, 1));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x8a}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[-1] = m0;
            top[0] = m1;
            top[1] = m10;
            top += 1;
            MONAD_AOT_TAIL return b_26e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_26e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j5) { MONAD_AOT_TAIL return b_2f9<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_276<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_276(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x61, 0x99, 0x9a, 0x61, 0x91, 0x83, 0x51, 0x61, 0x81, 0x61, 0x60, 0x82, 0x01, 0x80, 0x95, 0x61, 0x56}, 13, 7));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x61, 0x99, 0x9a, 0x61, 0x91, 0x83, 0x51, 0x61, 0x81, 0x61, 0x60, 0x82, 0x01, 0x80, 0x95, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-12] = m11;
            top[-11] = uint256_t{0x2f6ull};
            top[-2] = uint256_t{0x2edull};
            top[-1] = m12;
            top[0] = t2;
            top[1] = t1;
            top[2] = uint256_t{0x2a0ull};
            top[3] = t1;
            top[4] = uint256_t{0x294ull};
            top[5] = t2;
            top[6] = m2;
            top += 6;
            MONAD_AOT_TAIL return b_1f66<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_294(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x03, 0x84, 0x81, 0x01, 0x83, 0x52, 0x82, 0x61, 0x56}, 6, 1));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x03, 0x84, 0x81, 0x01, 0x83, 0x52, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = t1 + s5;
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, t2);
            uint256_t const m3 = s3;
            top[-1] = t1;
            top[0] = m3;
            MONAD_AOT_TAIL return b_1437<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2a0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x90, 0x20, 0x60, 0x89, 0x81, 0x01, 0x51, 0x85, 0x8b, 0x01, 0x51, 0x95, 0x51, 0x91, 0x82, 0x01, 0x96, 0x87, 0x52, 0x60, 0x82, 0x01, 0x92, 0x90, 0x92, 0x52, 0x33, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x81, 0x01, 0x93, 0x90, 0x93, 0x52, 0x60, 0x35, 0x60, 0x84, 0x01, 0x52, 0x82, 0x60, 0x81, 0x01}, 10, 3));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x90, 0x20, 0x60, 0x89, 0x81, 0x01, 0x51, 0x85, 0x8b, 0x01, 0x51, 0x95, 0x51, 0x91, 0x82, 0x01, 0x96, 0x87, 0x52, 0x60, 0x82, 0x01, 0x92, 0x90, 0x92, 0x52, 0x33, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x81, 0x01, 0x93, 0x90, 0x93, 0x52, 0x60, 0x35, 0x60, 0x84, 0x01, 0x52, 0x82, 0x60, 0x81, 0x01}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            auto const h3 = aot::sha3_any<traits>(ctx, gas, s1, t1);
            gas = ctx->gas_remaining;
            uint256_t const &s9 = top[-9];
            uint256_t const t2 = uint256_t{0x20ull} + s9;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const &s4 = top[-4];
            uint256_t const t4 = s9 + s4;
            uint256_t const t5 = aot::mload<traits>(ctx, gas, t4);
            uint256_t const t6 = aot::mload<traits>(ctx, gas, s4);
            uint256_t const t7 = t6 + uint256_t{0x20ull};
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, t7, s5);
            uint256_t const t8 = t6 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t8, h3);
            uint256_t const t9 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t10 = t6 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t10, t9);
            uint256_t const t11 = t6 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t11, t3);
            uint256_t const t12 = t6 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t12, t5);
            uint256_t const t13 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const t14 = t6 + uint256_t{0xc0ull};
            aot::mstore<traits>(ctx, gas, t14, t13);
            uint256_t const t15 = t6 + uint256_t{0xe0ull};
            top[-5] = t7;
            top[-4] = t6;
            top[-1] = t6;
            top[0] = t15;
            MONAD_AOT_TAIL return b_2e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2e1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x03, 0x90, 0x81, 0x01, 0x83, 0x52, 0x82, 0x61, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x03, 0x90, 0x81, 0x01, 0x83, 0x52, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = t1 + s2;
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, s4, t2);
            uint256_t const m4 = s4;
            top[-2] = t1;
            top[-1] = m4;
            top += -1;
            MONAD_AOT_TAIL return b_1437<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2ed(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x90, 0x20, 0x93, 0x61, 0x56}, 6, 0));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x90, 0x20, 0x93, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            auto const h3 = aot::sha3_any<traits>(ctx, gas, s1, t1);
            gas = ctx->gas_remaining;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-5] = h3;
            top[-1] = m5;
            top += -1;
            MONAD_AOT_TAIL return b_1cf7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2f6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0xf3}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::finish(ctx, gas, StatusCode::Success, s0, s0);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2f9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x61, 0x61, 0x93, 0x8c, 0x51, 0x61, 0x56}, 9, 6));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x61, 0x61, 0x93, 0x8c, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s8);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x321ull};
            top[1] = m0;
            top[2] = uint256_t{0x311ull};
            top[3] = uint256_t{0x30bull};
            top[4] = m0;
            top[5] = t1;
            top += 5;
            MONAD_AOT_TAIL return b_175e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_30b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x61, 0x56}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            top[0] = t1;
            MONAD_AOT_TAIL return b_2054<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_311(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x82, 0x86, 0x61, 0x56}, 5, 4));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x82, 0x86, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[1] = uint256_t{0x31bull};
            top[2] = m1;
            top[3] = m4;
            top += 3;
            MONAD_AOT_TAIL return b_175e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_31b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x52, 0x61, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s0, s1);
            top += -2;
            MONAD_AOT_TAIL return b_1f0a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_321(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_26e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_342(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x80ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x336); }
            MONAD_AOT_TAIL return b_36c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_36c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x67, 0x90, 0x80, 0x35, 0x82, 0x81, 0x11, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x67, 0x90, 0x80, 0x35, 0x82, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j8 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            top[0] = uint256_t{0xffffffffffffffffull};
            top[1] = m0;
            top[2] = t1;
            top += 2;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x332); }
            MONAD_AOT_TAIL return b_37f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_37f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x83, 0x01, 0x61, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x83, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s1 + s0;
            top[0] = uint256_t{0x38bull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_164b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_396(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x84, 0x01, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x84, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s2 + s0;
            top[0] = uint256_t{0x3a2ull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_161a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3b9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x91, 0x36, 0x91, 0x01, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x91, 0x36, 0x91, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s0 + s1;
            top[-1] = uint256_t{0x3c4ull};
            top[0] = t1;
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_15c1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3df(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x61, 0x97, 0x98, 0x81, 0x51, 0x61, 0x81, 0x61, 0x60, 0x82, 0x01, 0x80, 0x95, 0x61, 0x56}, 11, 6));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x61, 0x97, 0x98, 0x81, 0x51, 0x61, 0x81, 0x61, 0x60, 0x82, 0x01, 0x80, 0x95, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[-10] = m9;
            top[-9] = uint256_t{0x2f6ull};
            top[-1] = t2;
            top[0] = t1;
            top[1] = uint256_t{0x425ull};
            top[2] = t1;
            top[3] = uint256_t{0x3f9ull};
            top[4] = t2;
            top[5] = m10;
            top += 5;
            MONAD_AOT_TAIL return b_1f66<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3f9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x03, 0x7f, 0x81, 0x01, 0x83, 0x52, 0x82, 0x61, 0x56}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x03, 0x7f, 0x81, 0x01, 0x83, 0x52, 0x82, 0x61, 0x56}) + 0;
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
            MONAD_AOT_TAIL return b_1437<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4ab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x90, 0x81, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x90, 0x81, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j8 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x20ull};
            top[1] = m0;
            top += 1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x332); }
            MONAD_AOT_TAIL return b_4d7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4d7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x35, 0x90, 0x67, 0x82, 0x11, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x35, 0x90, 0x67, 0x82, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j7 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x32e); }
            MONAD_AOT_TAIL return b_4e9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4e9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x91, 0x36, 0x91, 0x01, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x91, 0x36, 0x91, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s0 + s1;
            top[-1] = uint256_t{0x4f4ull};
            top[0] = t1;
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_161a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_501(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x85, 0x80, 0xf3}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x85, 0x80, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            aot::finish(ctx, gas, StatusCode::Success, s5, s5);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_515(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_197c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_5ca(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x60ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x336); }
            MONAD_AOT_TAIL return b_5f4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_5f4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x81, 0x61, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x81, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x676ull};
            top[2] = m0;
            top[3] = uint256_t{0x5ffull};
            top += 3;
            MONAD_AOT_TAIL return b_14a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_67a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j4 = aot::nonzero(t1);
            top += -1;
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x336); }
            MONAD_AOT_TAIL return b_681<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_681(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x80ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x336); }
            MONAD_AOT_TAIL return b_6ab<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6ab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x6b2ull};
            top += 1;
            MONAD_AOT_TAIL return b_14a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_6b2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            top[1] = uint256_t{0x6bbull};
            top += 1;
            MONAD_AOT_TAIL return b_14c3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_6bb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x61, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[0] = m2;
            top[1] = uint256_t{0x6c4ull};
            top += 1;
            MONAD_AOT_TAIL return b_14e6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_6c4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x65, 0x92, 0x60, 0x35, 0x84, 0x81, 0x16, 0x90, 0x81, 0x81, 0x03, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x65, 0x92, 0x60, 0x35, 0x84, 0x81, 0x16, 0x90, 0x81, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffull};
            uint256_t const t3 = t1 - t2;
            bool const j13 = aot::nonzero(t3);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = uint256_t{0xffffffffffffull};
            top[1] = m2;
            top[2] = t2;
            top[3] = t1;
            top += 3;
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x32a); }
            MONAD_AOT_TAIL return b_6db<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6db(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x79, 0x94, 0x7f, 0x94, 0x33, 0x8a, 0x52, 0x60, 0x60, 0x52, 0x7f, 0x85, 0x8b, 0x20, 0x98, 0x73, 0x80, 0x94, 0x16, 0x99, 0x8a, 0x8d, 0x52, 0x60, 0x52, 0x83, 0x87, 0x8d, 0x20, 0x9b, 0x16, 0x9a, 0x8b, 0x8d, 0x52, 0x60, 0x52, 0x86, 0x8c, 0x20, 0x94, 0x86, 0x15, 0x60, 0x14, 0x61, 0x57}, 8, 7));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x79, 0x94, 0x7f, 0x94, 0x33, 0x8a, 0x52, 0x60, 0x60, 0x52, 0x7f, 0x85, 0x8b, 0x20, 0x98, 0x73, 0x80, 0x94, 0x16, 0x99, 0x8a, 0x8d, 0x52, 0x60, 0x52, 0x83, 0x87, 0x8d, 0x20, 0x9b, 0x16, 0x9a, 0x8b, 0x8d, 0x52, 0x60, 0x52, 0x86, 0x8c, 0x20, 0x94, 0x86, 0x15, 0x60, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s7 = top[-7];
            aot::mstore<traits>(ctx, gas, s7, t1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x1ull});
            uint256_t const &s2 = top[-2];
            auto const h13 = aot::sha3_any<traits>(ctx, gas, s7, s2);
            gas = ctx->gas_remaining;
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = s4 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore<traits>(ctx, gas, s7, t2);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, h13);
            auto const h28 = aot::sha3_any<traits>(ctx, gas, s7, s2);
            gas = ctx->gas_remaining;
            uint256_t const &s6 = top[-6];
            uint256_t const t3 = s6 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore<traits>(ctx, gas, s7, t3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, h28);
            auto const h39 = aot::sha3_any<traits>(ctx, gas, s7, s2);
            gas = ctx->gas_remaining;
            uint256_t const &s1 = top[-1];
            uint256_t const t4 = aot::from_bool(!aot::nonzero(s1));
            uint256_t const t5 = aot::from_bool(uint256_t{0x0ull} == t4);
            bool const j46 = aot::nonzero(t5);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-6] = t3;
            top[-5] = t2;
            top[-4] = uint256_t{0x0ull, 0x0ull, 0xffffffff00000000ull, 0xffffull};
            top[-3] = uint256_t{0xc112deffd817036bull, 0xbec047c5a52207b9ull, 0x7d0161b249b1ab8bull, 0xda9fa7c1b00402c1ull};
            top[0] = h39;
            top[1] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[2] = m3;
            top[3] = uint256_t{0x0ull, 0x0ull, 0x0ull, 0xffffffffffff0000ull};
            top[4] = m5;
            top[5] = m0;
            top += 5;
            if (j46) { MONAD_AOT_TAIL return b_7a4<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_77f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_77f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x42, 0x16, 0x92}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x42, 0x16, 0x92}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 & s1;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-4] = t2;
            top[-1] = m4;
            top += -1;
            MONAD_AOT_TAIL return b_783<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_783(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x54, 0x92, 0x16, 0x97, 0x88, 0x93, 0x60, 0x1b, 0x16, 0x91, 0x16, 0x17, 0x17, 0x90, 0x55, 0x81, 0x51, 0x93, 0x84, 0x52, 0x60, 0x84, 0x01, 0x52, 0x33, 0x92, 0xa4, 0x80, 0xf3}, 12, 2));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x54, 0x92, 0x16, 0x97, 0x88, 0x93, 0x60, 0x1b, 0x16, 0x91, 0x16, 0x17, 0x17, 0x90, 0x55, 0x81, 0x51, 0x93, 0x84, 0x52, 0x60, 0x84, 0x01, 0x52, 0x33, 0x92, 0xa4, 0x80, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::sload<traits>(ctx, gas, s4);
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s2 & s0;
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = aot::shl_c<160>(s3);
            uint256_t const &s8 = top[-8];
            uint256_t const t4 = t3 & s8;
            uint256_t const &s1 = top[-1];
            uint256_t const t5 = t1 & s1;
            uint256_t const t6 = t5 | t4;
            uint256_t const t7 = t6 | t2;
            aot::sstore<traits>(ctx, gas, s4, t7, (aot::gas_of<traits>({0x81, 0x51, 0x93, 0x84, 0x52, 0x60, 0x84, 0x01, 0x52, 0x33, 0x92, 0xa4, 0x80, 0xf3}) + 0));
            uint256_t const &s6 = top[-6];
            uint256_t const t8 = aot::mload<traits>(ctx, gas, s6);
            aot::mstore<traits>(ctx, gas, t8, t2);
            uint256_t const t9 = t8 + uint256_t{0x20ull};
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, t9, s5);
            uint256_t const t10 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s7 = top[-7];
            uint256_t const &s9 = top[-9];
            uint256_t const &s10 = top[-10];
            ctx->gas_remaining = gas;
            runtime::log4<traits>(ctx, &t8, &s6, &s7, &t10, &s9, &s10);
            gas = ctx->gas_remaining;
            uint256_t const &s11 = top[-11];
            aot::finish(ctx, gas, StatusCode::Success, s11, s11);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_7a4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x92, 0x61, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x92, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-4] = m0;
            top[-1] = m4;
            top += -1;
            MONAD_AOT_TAIL return b_783<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_7b4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x60ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x5bf); }
            MONAD_AOT_TAIL return b_7de<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_7de(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x7e5ull};
            top += 1;
            MONAD_AOT_TAIL return b_14a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_806(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x33, 0x88, 0x52, 0x60, 0x91, 0x60, 0x83, 0x52, 0x84, 0x89, 0x20, 0x96, 0x73, 0x80, 0x91, 0x16, 0x97, 0x88, 0x8b, 0x52, 0x84, 0x52, 0x85, 0x8a, 0x20, 0x98, 0x16, 0x97, 0x88, 0x8a, 0x52, 0x83, 0x52, 0x84, 0x89, 0x20, 0x54, 0x60, 0x1c, 0x93, 0x84, 0x87, 0x11, 0x15, 0x61, 0x57}, 8, 5));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x33, 0x88, 0x52, 0x60, 0x91, 0x60, 0x83, 0x52, 0x84, 0x89, 0x20, 0x96, 0x73, 0x80, 0x91, 0x16, 0x97, 0x88, 0x8b, 0x52, 0x84, 0x52, 0x85, 0x8a, 0x20, 0x98, 0x16, 0x97, 0x88, 0x8a, 0x52, 0x83, 0x52, 0x84, 0x89, 0x20, 0x54, 0x60, 0x1c, 0x93, 0x84, 0x87, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s7 = top[-7];
            aot::mstore<traits>(ctx, gas, s7, t1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x1ull});
            uint256_t const &s3 = top[-3];
            auto const h10 = aot::sha3_any<traits>(ctx, gas, s7, s3);
            gas = ctx->gas_remaining;
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = s5 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore<traits>(ctx, gas, s7, t2);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, h10);
            auto const h24 = aot::sha3_any<traits>(ctx, gas, s7, s3);
            gas = ctx->gas_remaining;
            uint256_t const &s6 = top[-6];
            uint256_t const t3 = s6 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore<traits>(ctx, gas, s7, t3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, h24);
            auto const h35 = aot::sha3_any<traits>(ctx, gas, s7, s3);
            gas = ctx->gas_remaining;
            uint256_t const t4 = aot::sload<traits>(ctx, gas, h35);
            uint256_t const t5 = aot::shr_c<208>(t4);
            uint256_t const &s4 = top[-4];
            uint256_t const t6 = aot::from_bool(t5 < s4);
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            bool const j45 = aot::nonzero(t7);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-6] = t3;
            top[-5] = t2;
            top[-2] = t5;
            top[-1] = uint256_t{0x20ull};
            top[1] = m1;
            top[2] = m2;
            top += 2;
            if (j45) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x917); }
            MONAD_AOT_TAIL return b_84d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_84d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x85, 0x84, 0x03, 0x16, 0x11, 0x61, 0x57}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x85, 0x84, 0x03, 0x16, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s2 - s4;
            uint256_t const &s0 = top[0];
            uint256_t const t2 = t1 & s0;
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffull} < t2);
            bool const j8 = aot::nonzero(t3);
            top += -1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x8f0); }
            MONAD_AOT_TAIL return b_85a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_85a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x90, 0x7f, 0x93, 0x92, 0x91, 0x33, 0x89, 0x52, 0x60, 0x82, 0x52, 0x83, 0x89, 0x20, 0x87, 0x8a, 0x52, 0x82, 0x52, 0x83, 0x89, 0x20, 0x88, 0x8a, 0x52, 0x82, 0x52, 0x83, 0x89, 0x20, 0x90, 0x79, 0x7f, 0x83, 0x54, 0x92, 0x60, 0x1b, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x82, 0x51, 0x94, 0x85, 0x52, 0x84, 0x01, 0x52, 0x33, 0x92, 0xa4, 0x80, 0xf3}, 9, 5));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x90, 0x7f, 0x93, 0x92, 0x91, 0x33, 0x89, 0x52, 0x60, 0x82, 0x52, 0x83, 0x89, 0x20, 0x87, 0x8a, 0x52, 0x82, 0x52, 0x83, 0x89, 0x20, 0x88, 0x8a, 0x52, 0x82, 0x52, 0x83, 0x89, 0x20, 0x90, 0x79, 0x7f, 0x83, 0x54, 0x92, 0x60, 0x1b, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x82, 0x51, 0x94, 0x85, 0x52, 0x84, 0x01, 0x52, 0x33, 0x92, 0xa4, 0x80, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, s8, t1);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, uint256_t{0x1ull});
            uint256_t const &s4 = top[-4];
            auto const h14 = aot::sha3_any<traits>(ctx, gas, s8, s4);
            gas = ctx->gas_remaining;
            uint256_t const &s6 = top[-6];
            aot::mstore<traits>(ctx, gas, s8, s6);
            aot::mstore<traits>(ctx, gas, s2, h14);
            auto const h22 = aot::sha3_any<traits>(ctx, gas, s8, s4);
            gas = ctx->gas_remaining;
            uint256_t const &s7 = top[-7];
            aot::mstore<traits>(ctx, gas, s8, s7);
            aot::mstore<traits>(ctx, gas, s2, h22);
            auto const h30 = aot::sha3_any<traits>(ctx, gas, s8, s4);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::sload<traits>(ctx, gas, h30);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::shl_c<208>(s1);
            uint256_t const t4 = t3 & uint256_t{0x0ull, 0x0ull, 0x0ull, 0xffffffffffff0000ull};
            uint256_t const t5 = t2 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffull};
            uint256_t const t6 = t5 | t4;
            aot::sstore<traits>(ctx, gas, h30, t6, (aot::gas_of<traits>({0x82, 0x51, 0x94, 0x85, 0x52, 0x84, 0x01, 0x52, 0x33, 0x92, 0xa4, 0x80, 0xf3}) + 0));
            uint256_t const t7 = aot::mload<traits>(ctx, gas, s4);
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, t7, s5);
            uint256_t const t8 = t7 + s2;
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, t8, s3);
            uint256_t const t9 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const k55_2 = uint256_t{0x284dfb1c246418f3ull, 0x2b2259abd7415ca2ull, 0x35a8e7e25395ff7full, 0x55eb90d810e1700bull};
            ctx->gas_remaining = gas;
            runtime::log4<traits>(ctx, &t7, &s4, &k55_2, &t9, &s6, &s7);
            gas = ctx->gas_remaining;
            aot::finish(ctx, gas, StatusCode::Success, s8, s8);
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_946(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s0 = top[0];
            uint256_t const t3 = aot::from_bool(slt(t2, s0));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x336); }
            MONAD_AOT_TAIL return b_96f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_96f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x60, 0x92, 0x73, 0x61, 0x61, 0x56}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x60, 0x92, 0x73, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = uint256_t{0x20ull};
            top[1] = m0;
            top[2] = m1;
            top[3] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[4] = uint256_t{0x98full};
            top += 4;
            MONAD_AOT_TAIL return b_14a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9b0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::from_bool(slt(t2, s1));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x5bf); }
            MONAD_AOT_TAIL return b_9d9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9d9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x90, 0x35, 0x91, 0x60, 0x35, 0x33, 0x85, 0x52, 0x84, 0x60, 0x52, 0x81, 0x85, 0x20, 0x84, 0x86, 0x52, 0x60, 0x52, 0x81, 0x85, 0x20, 0x81, 0x81, 0x54, 0x17, 0x90, 0x55, 0x81, 0x51, 0x93, 0x84, 0x52, 0x60, 0x84, 0x01, 0x52, 0x33, 0x92, 0xa2, 0x80, 0xf3}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x90, 0x35, 0x91, 0x60, 0x35, 0x33, 0x85, 0x52, 0x84, 0x60, 0x52, 0x81, 0x85, 0x20, 0x84, 0x86, 0x52, 0x60, 0x52, 0x81, 0x85, 0x20, 0x81, 0x81, 0x54, 0x17, 0x90, 0x55, 0x81, 0x51, 0x93, 0x84, 0x52, 0x60, 0x84, 0x01, 0x52, 0x33, 0x92, 0xa2, 0x80, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t3 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, t3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, s2);
            uint256_t const &s1 = top[-1];
            auto const h14 = aot::sha3_any<traits>(ctx, gas, s2, s1);
            gas = ctx->gas_remaining;
            aot::mstore<traits>(ctx, gas, s2, t1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, h14);
            auto const h22 = aot::sha3_any<traits>(ctx, gas, s2, s1);
            gas = ctx->gas_remaining;
            uint256_t const t4 = aot::sload<traits>(ctx, gas, h22);
            uint256_t const t5 = t4 | t2;
            aot::sstore<traits>(ctx, gas, h22, t5, (aot::gas_of<traits>({0x81, 0x51, 0x93, 0x84, 0x52, 0x60, 0x84, 0x01, 0x52, 0x33, 0x92, 0xa2, 0x80, 0xf3}) + 0));
            uint256_t const t6 = aot::mload<traits>(ctx, gas, s1);
            aot::mstore<traits>(ctx, gas, t6, t1);
            uint256_t const t7 = t6 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t7, t2);
            uint256_t const t8 = runtime::uint256_from_address(ctx->env.sender);
            aot::log2<traits>(ctx, gas, t6, s1, uint256_t{0xda8843b3f46b918dull, 0xb1dd12f6e9e99648ull, 0xe561bbaab6e6cdc1ull, 0x3704902f963766a4ull}, t8);
            gas = ctx->gas_remaining;
            aot::finish(ctx, gas, StatusCode::Success, s2, s2);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a28(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x34, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j4 = aot::nonzero(t1);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[1] = m2;
            top += 1;
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xa9a); }
            MONAD_AOT_TAIL return b_a2f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a2f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x80ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xa9a); }
            MONAD_AOT_TAIL return b_a59<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a59(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0xa60ull};
            top += 1;
            MONAD_AOT_TAIL return b_14a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a60(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0xa68ull};
            top += 1;
            MONAD_AOT_TAIL return b_14c3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a68(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0xa70ull};
            top += 1;
            MONAD_AOT_TAIL return b_14e6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a70(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x91, 0x73, 0x83, 0x16, 0x83, 0x03, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x91, 0x73, 0x83, 0x16, 0x83, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = t1 - t2;
            bool const j10 = aot::nonzero(t3);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[1] = m1;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x32e); }
            MONAD_AOT_TAIL return b_a92<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a92(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x93, 0x61, 0x56}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x93, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = uint256_t{0x2f6ull};
            top[1] = m3;
            top += 1;
            MONAD_AOT_TAIL return b_17a1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_aa4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::from_bool(slt(t2, s1));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x336); }
            MONAD_AOT_TAIL return b_acd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_acd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x90, 0x61, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x90, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x20ull};
            top[1] = m0;
            top[2] = uint256_t{0xad7ull};
            top += 2;
            MONAD_AOT_TAIL return b_1b1e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ade(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x82, 0x90, 0x34, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x82, 0x90, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j6 = aot::nonzero(t1);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = m3;
            top[0] = m1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x5bf); }
            MONAD_AOT_TAIL return b_ae7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ae7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x100ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x5bf); }
            MONAD_AOT_TAIL return b_b12<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b12(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x36, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x36, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            top[1] = uint256_t{0xb1aull};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_152a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_b1a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x80, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x80, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xffffffffffffff7cull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::from_bool(slt(t2, s1));
            bool const j8 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m1 = s1;
            top[-1] = m0;
            top[0] = m1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x332); }
            MONAD_AOT_TAIL return b_b45<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b45(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0xb4cull};
            top += 1;
            MONAD_AOT_TAIL return b_1478<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_b4c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x60, 0x35, 0x67, 0x81, 0x11, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x60, 0x35, 0x67, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xe4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j8 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[0] = m2;
            top[1] = t1;
            top += 1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xbda); }
            MONAD_AOT_TAIL return b_b60<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b60(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x94, 0x61, 0x91, 0x36, 0x91, 0x01, 0x61, 0x56}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x94, 0x61, 0x91, 0x36, 0x91, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s4 = top[-4];
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s4 + s0;
            top[-4] = uint256_t{0x2f6ull};
            top[0] = uint256_t{0xb6full};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_15c1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_b6f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x93, 0x90, 0x92, 0x61, 0x83, 0x51, 0x61, 0x56}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x93, 0x90, 0x92, 0x61, 0x83, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-4] = m0;
            top[-3] = m1;
            top[-1] = m4;
            top[0] = m3;
            top[1] = uint256_t{0xb7cull};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_2054<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_b7c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x84, 0x01, 0x51, 0x82, 0x85, 0x01, 0x51, 0x90, 0x83, 0x51, 0x92, 0x60, 0x84, 0x01, 0x94, 0x7f, 0x86, 0x52, 0x84, 0x01, 0x52, 0x33, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x61, 0x81, 0x61, 0x56}, 4, 6));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x84, 0x01, 0x51, 0x82, 0x85, 0x01, 0x51, 0x90, 0x83, 0x51, 0x92, 0x60, 0x84, 0x01, 0x94, 0x7f, 0x86, 0x52, 0x84, 0x01, 0x52, 0x33, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x20ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = s3 + s1;
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const t5 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const t6 = t5 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t6, uint256_t{0x714604c986d80106ull, 0xd39f6583d6ec6b35ull, 0x9a2404a1d46691e4ull, 0x939c21a48a8dbe3aull});
            uint256_t const t7 = t5 + s1;
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t7, s0);
            uint256_t const t8 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t9 = t5 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t9, t8);
            uint256_t const t10 = t5 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t10, t2);
            uint256_t const t11 = t5 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t11, t4);
            aot::mstore<traits>(ctx, gas, t5, uint256_t{0xa0ull});
            top[-1] = t6;
            top[0] = t5;
            top[1] = uint256_t{0xbd1ull};
            top[2] = t5;
            top += 2;
            MONAD_AOT_TAIL return b_141b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_bd1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x90, 0x20, 0x91, 0x61, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x90, 0x20, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            auto const h3 = aot::sha3_any<traits>(ctx, gas, s1, t1);
            gas = ctx->gas_remaining;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = h3;
            top[-1] = m3;
            top += -1;
            MONAD_AOT_TAIL return b_1c25<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_bde(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x91, 0x34, 0x61, 0x57}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x91, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j5 = aot::nonzero(t1);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = m1;
            top[-1] = m3;
            top += -1;
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x336); }
            MONAD_AOT_TAIL return b_be6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_be6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x100ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x336); }
            MONAD_AOT_TAIL return b_c11<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c11(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0xc18ull};
            top += 1;
            MONAD_AOT_TAIL return b_14a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c18(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x36, 0x01, 0x60, 0x81, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x36, 0x01, 0x60, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xffffffffffffffdcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0xc0ull}));
            bool const j8 = aot::nonzero(t3);
            top[1] = t2;
            top += 1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x332); }
            MONAD_AOT_TAIL return b_c44<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c44(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x85, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}, 5, 5));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x85, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s4);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = uint256_t{0x80ull};
            top[2] = m0;
            top[3] = uint256_t{0xc51ull};
            top[4] = t1;
            top += 4;
            MONAD_AOT_TAIL return b_13e3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c51(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x12, 0x61, 0x57}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(slt(s0, s1));
            bool const j3 = aot::nonzero(t1);
            top += -2;
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x332); }
            MONAD_AOT_TAIL return b_c57<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c57(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x84, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 5, 4));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x84, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s4);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0xc62ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_1398<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_c62(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x91, 0x60, 0x35, 0x83, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x91, 0x60, 0x35, 0x83, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = t1 - t2;
            bool const j11 = aot::nonzero(t3);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[1] = m1;
            top[2] = t1;
            top += 2;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x49f); }
            MONAD_AOT_TAIL return b_c85<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c85(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x52, 0x60, 0x35, 0x83, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x52, 0x60, 0x35, 0x83, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s1, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const &s3 = top[-3];
            uint256_t const t2 = t1 & s3;
            uint256_t const t3 = t1 - t2;
            bool const j10 = aot::nonzero(t3);
            top[0] = t1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x49f); }
            MONAD_AOT_TAIL return b_c93<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c93(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x82, 0x01, 0x52, 0x65, 0x60, 0x35, 0x81, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x82, 0x01, 0x52, 0x65, 0x60, 0x35, 0x81, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const t3 = t2 & uint256_t{0xffffffffffffull};
            uint256_t const t4 = t2 - t3;
            bool const j13 = aot::nonzero(t4);
            top[0] = uint256_t{0xffffffffffffull};
            top[1] = t2;
            top += 1;
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x32a); }
            MONAD_AOT_TAIL return b_cab<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_cab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x88, 0x83, 0x01, 0x52, 0x60, 0x35, 0x90, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}, 9, 2));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x88, 0x83, 0x01, 0x52, 0x60, 0x35, 0x90, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = s2 + s8;
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = t2 & s1;
            uint256_t const t4 = t2 - t3;
            bool const j12 = aot::nonzero(t4);
            top[-1] = t2;
            top += -1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x49f); }
            MONAD_AOT_TAIL return b_cbb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_cbb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x82, 0x01, 0x52, 0x81, 0x52, 0x60, 0x35, 0x93, 0x82, 0x85, 0x16, 0x85, 0x03, 0x61, 0x57}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x82, 0x01, 0x52, 0x81, 0x52, 0x60, 0x35, 0x93, 0x82, 0x85, 0x16, 0x85, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x60ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, s1);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = t2 & s3;
            uint256_t const t4 = t2 - t3;
            bool const j15 = aot::nonzero(t4);
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-5] = t2;
            top[-1] = m5;
            top += -1;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xbda); }
            MONAD_AOT_TAIL return b_ccf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ccf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x82, 0x01, 0x94, 0x85, 0x52, 0x60, 0x35, 0x90, 0x87, 0x83, 0x01, 0x82, 0x81, 0x52, 0x60, 0x35, 0x67, 0x81, 0x11, 0x61, 0x57}, 7, 5));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x82, 0x01, 0x94, 0x85, 0x52, 0x60, 0x35, 0x90, 0x87, 0x83, 0x01, 0x82, 0x81, 0x52, 0x60, 0x35, 0x67, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, t1, s4);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0xc4ull});
            uint256_t const &s6 = top[-6];
            uint256_t const t3 = s1 + s6;
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = aot::calldataload(ctx, uint256_t{0xe4ull});
            uint256_t const t5 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t4);
            bool const j21 = aot::nonzero(t5);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-4] = t1;
            top[0] = t2;
            top[1] = m0;
            top[2] = t3;
            top[3] = t4;
            top += 3;
            if (j21) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x326); }
            MONAD_AOT_TAIL return b_cf2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_cf2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x84, 0x01, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x84, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s2 + s0;
            top[0] = uint256_t{0xcfeull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_15c1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_cfe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x90, 0x93, 0x80, 0x42, 0x11, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x90, 0x93, 0x80, 0x42, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = aot::from_bool(s4 < t1);
            bool const j8 = aot::nonzero(t2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const m4 = s4;
            top[-4] = m1;
            top[-3] = m0;
            top[-1] = m3;
            top[0] = m4;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xd88); }
            MONAD_AOT_TAIL return b_d09<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d09(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x91, 0x85, 0x91, 0x61, 0x61, 0x99, 0x9a, 0x61, 0x95, 0x61, 0x88, 0x51, 0x61, 0x56}, 11, 5));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x91, 0x85, 0x91, 0x61, 0x61, 0x99, 0x9a, 0x61, 0x95, 0x61, 0x88, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s5);
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-10] = m9;
            top[-9] = uint256_t{0x2f6ull};
            top[-4] = uint256_t{0xd7eull};
            top[-3] = m7;
            top[-2] = m4;
            top[-1] = m3;
            top[0] = uint256_t{0xd78ull};
            top[1] = m10;
            top[2] = m2;
            top[3] = uint256_t{0xd23ull};
            top[4] = t1;
            top += 4;
            MONAD_AOT_TAIL return b_1fbe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d23(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x89, 0x8c, 0x51, 0x16, 0x90, 0x51, 0x90, 0x83, 0x51, 0x92, 0x60, 0x84, 0x01, 0x94, 0x7f, 0x86, 0x52, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x61, 0x81, 0x61, 0x56}, 12, 5));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x89, 0x8c, 0x51, 0x16, 0x90, 0x51, 0x90, 0x83, 0x51, 0x92, 0x60, 0x84, 0x01, 0x94, 0x7f, 0x86, 0x52, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s11);
            uint256_t const &s9 = top[-9];
            uint256_t const t2 = t1 & s9;
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const t5 = t4 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t5, uint256_t{0x5a7a5626e310f3d0ull, 0xce40f282c88a8e90ull, 0x6a6327b620b67997ull, 0xf3841cd1ff008502ull});
            uint256_t const t6 = t4 + s2;
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t6, s0);
            uint256_t const t7 = t4 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t7, t2);
            uint256_t const t8 = t4 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t8, t3);
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x80ull});
            top[-2] = t5;
            top[-1] = t4;
            top[0] = uint256_t{0xd70ull};
            top[1] = t4;
            top += 1;
            MONAD_AOT_TAIL return b_13ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d70(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x90, 0x20, 0x61, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x90, 0x20, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            auto const h3 = aot::sha3_any<traits>(ctx, gas, s1, t1);
            gas = ctx->gas_remaining;
            top[-1] = h3;
            top += -1;
            MONAD_AOT_TAIL return b_1bd9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d78(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x61, 0x56}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[0] = m2;
            MONAD_AOT_TAIL return b_20c7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d7e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x92, 0x51, 0x16, 0x91, 0x61, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x92, 0x51, 0x16, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s3 = top[-3];
            uint256_t const t2 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = t2 & s1;
            top[-3] = t3;
            top[-1] = t1;
            top += -1;
            MONAD_AOT_TAIL return b_199d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_db7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x91, 0x34, 0x61, 0x57}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x91, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j5 = aot::nonzero(t1);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = m1;
            top[-1] = m3;
            top += -1;
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x336); }
            MONAD_AOT_TAIL return b_dbf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_dbf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x93, 0x81, 0x85, 0x36, 0x01, 0x12, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x93, 0x81, 0x85, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x60ull}));
            bool const j9 = aot::nonzero(t3);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            top[1] = uint256_t{0x60ull};
            top[2] = m2;
            top += 2;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x332); }
            MONAD_AOT_TAIL return b_dec<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_dec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0xdf3ull};
            top += 1;
            MONAD_AOT_TAIL return b_14a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_df3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x60, 0x90, 0x81, 0x35, 0x92, 0x67, 0x97, 0x88, 0x85, 0x11, 0x61, 0x57}, 6, 5));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x60, 0x90, 0x81, 0x35, 0x92, 0x67, 0x97, 0x88, 0x85, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j13 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-5] = uint256_t{0xffffffffffffffffull};
            top[-3] = m0;
            top[-1] = t1;
            top[0] = uint256_t{0x24ull};
            top[1] = m3;
            top[2] = m1;
            top[3] = m5;
            top += 3;
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x32a); }
            MONAD_AOT_TAIL return b_e0c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e0c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x85, 0x90, 0x85, 0x36, 0x03, 0x01, 0x12, 0x61, 0x57}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x85, 0x90, 0x85, 0x36, 0x03, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = t1 - s4;
            uint256_t const &s0 = top[0];
            uint256_t const t3 = t2 + s0;
            uint256_t const &s5 = top[-5];
            uint256_t const t4 = aot::from_bool(slt(t3, s5));
            bool const j8 = aot::nonzero(t4);
            top += -1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x49f); }
            MONAD_AOT_TAIL return b_e17<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e17(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x51, 0x97, 0x85, 0x89, 0x01, 0x89, 0x81, 0x10, 0x82, 0x82, 0x11, 0x17, 0x61, 0x57}, 8, 5));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x51, 0x97, 0x85, 0x89, 0x01, 0x89, 0x81, 0x10, 0x82, 0x82, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = t1 + s4;
            uint256_t const t3 = aot::from_bool(t2 < t1);
            uint256_t const &s7 = top[-7];
            uint256_t const t4 = aot::from_bool(s7 < t2);
            uint256_t const t5 = t4 | t3;
            bool const j14 = aot::nonzero(t5);
            uint256_t const m7 = s7;
            top[-7] = t1;
            top[1] = m7;
            top[2] = t2;
            top += 2;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x104a); }
            MONAD_AOT_TAIL return b_e28<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e28(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x52, 0x84, 0x83, 0x01, 0x35, 0x81, 0x81, 0x11, 0x61, 0x57}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x52, 0x84, 0x83, 0x01, 0x35, 0x81, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s2, s0);
            uint256_t const &s3 = top[-3];
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = s3 + s5;
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::from_bool(s1 < t2);
            bool const j10 = aot::nonzero(t3);
            top[0] = t2;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x326); }
            MONAD_AOT_TAIL return b_e35<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e35(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x85, 0x01, 0x90, 0x36, 0x60, 0x83, 0x01, 0x12, 0x15, 0x61, 0x57}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x85, 0x01, 0x90, 0x36, 0x60, 0x83, 0x01, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s5 + s0;
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t3 = t1 + uint256_t{0x23ull};
            uint256_t const t4 = aot::from_bool(slt(t3, t2));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            bool const j10 = aot::nonzero(t5);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[0] = m1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x326); }
            MONAD_AOT_TAIL return b_e43<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e43(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x83, 0x82, 0x01, 0x35, 0x91, 0x61, 0x83, 0x61, 0x56}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x83, 0x82, 0x01, 0x35, 0x91, 0x61, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s1 + s3;
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const m1 = s1;
            top[-1] = t2;
            top[1] = m1;
            top[2] = uint256_t{0xe50ull};
            top[3] = t2;
            top += 3;
            MONAD_AOT_TAIL return b_15ef<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_e50(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x61, 0x85, 0x51, 0x92, 0x83, 0x61, 0x56}, 5, 4));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x61, 0x85, 0x51, 0x92, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s4);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = t1;
            top[0] = m1;
            top[1] = uint256_t{0xe5dull};
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_1437<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_e5d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x82, 0x52, 0x60, 0x93, 0x87, 0x85, 0x84, 0x01, 0x91, 0x60, 0x1b, 0x83, 0x01, 0x01, 0x91, 0x36, 0x83, 0x11, 0x61, 0x57}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x82, 0x52, 0x60, 0x93, 0x87, 0x85, 0x84, 0x01, 0x91, 0x60, 0x1b, 0x83, 0x01, 0x01, 0x91, 0x36, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s1, s3);
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            uint256_t const t2 = aot::shl_c<7>(s3);
            uint256_t const &s0 = top[0];
            uint256_t const t3 = s0 + t2;
            uint256_t const &s6 = top[-6];
            uint256_t const t4 = t3 + s6;
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t6 = aot::from_bool(t5 < t4);
            bool const j21 = aot::nonzero(t6);
            uint256_t const m0 = s0;
            top[-3] = uint256_t{0x20ull};
            top[0] = t4;
            top[1] = t1;
            top[2] = m0;
            top += 2;
            if (j21) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1046); }
            MONAD_AOT_TAIL return b_e77<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e77(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x88, 0x01, 0x90}, 9, 1));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x88, 0x01, 0x90}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s8 + s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[0] = m1;
            MONAD_AOT_TAIL return b_e7a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_e7a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x82, 0x10, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(s1 < s2);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_fe9<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_e82<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e82(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x8a, 0x52, 0x60, 0x61, 0x86, 0x88, 0x01, 0x61, 0x56}, 14, 0));
            if (MONAD_UNLIKELY(top - bottom < 14)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x8a, 0x52, 0x60, 0x61, 0x86, 0x88, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s13 = top[-13];
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s13, s3);
            uint256_t const &s9 = top[-9];
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = s9 + s8;
            top[-3] = uint256_t{0x44ull};
            top[-2] = uint256_t{0xe93ull};
            top[-1] = t1;
            top += -1;
            MONAD_AOT_TAIL return b_1509<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_e93(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x96, 0x83, 0x8c, 0x01, 0x97, 0x88, 0x52, 0x01, 0x35, 0x94, 0x83, 0x8b, 0x01, 0x91, 0x86, 0x83, 0x52, 0x60, 0x35, 0x90, 0x81, 0x11, 0x61, 0x57}, 12, 2));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x96, 0x83, 0x8c, 0x01, 0x97, 0x88, 0x52, 0x01, 0x35, 0x94, 0x83, 0x8b, 0x01, 0x91, 0x86, 0x83, 0x52, 0x60, 0x35, 0x90, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s11 + s3;
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const &s7 = top[-7];
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s7 + s1;
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const &s4 = top[-4];
            uint256_t const t4 = s11 + s4;
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const t5 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const &s2 = top[-2];
            uint256_t const t6 = aot::from_bool(s2 < t5);
            bool const j24 = aot::nonzero(t6);
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-7] = t1;
            top[-6] = t3;
            top[-2] = t4;
            top[-1] = m6;
            top[0] = t5;
            if (j24) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xfe5); }
            MONAD_AOT_TAIL return b_eaf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_eaf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x87, 0x01, 0x61, 0x56}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x87, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s5 = top[-5];
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s5 + s0;
            top[0] = uint256_t{0xebbull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_15c1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ebb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x95, 0x90, 0x96, 0x80, 0x42, 0x11, 0x61, 0x57}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x95, 0x90, 0x96, 0x80, 0x42, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const &s7 = top[-7];
            uint256_t const t2 = aot::from_bool(s7 < t1);
            bool const j8 = aot::nonzero(t2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const m7 = s7;
            top[-7] = m1;
            top[-6] = m0;
            top[-1] = m6;
            top[0] = m7;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xfba); }
            MONAD_AOT_TAIL return b_ec6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ec6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x89, 0x98, 0x99, 0x51, 0x51, 0x61, 0x81, 0x61, 0x56}, 13, 1));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x89, 0x98, 0x99, 0x51, 0x51, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s12 = top[-12];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s12);
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const m12 = s12;
            top[-12] = m11;
            top[-11] = m12;
            top[-2] = t2;
            top[-1] = uint256_t{0xed6ull};
            top[0] = t2;
            MONAD_AOT_TAIL return b_1ebb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ed6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x8b}, 12, 1));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x8b}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            top[-1] = m0;
            top[0] = m1;
            top[1] = m11;
            top += 1;
            MONAD_AOT_TAIL return b_ed9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ed9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j5) { MONAD_AOT_TAIL return b_f97<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_ee1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ee1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x92, 0x88, 0x94, 0x92, 0x61, 0x92, 0x61, 0x97, 0x95, 0x83, 0x51, 0x61, 0x81, 0x61, 0x86, 0x82, 0x01, 0x80, 0x95, 0x61, 0x56}, 11, 8));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x92, 0x88, 0x94, 0x92, 0x61, 0x92, 0x61, 0x97, 0x95, 0x83, 0x51, 0x61, 0x81, 0x61, 0x86, 0x82, 0x01, 0x80, 0x95, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s5);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = t1 + s4;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const m5 = s5;
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-7] = uint256_t{0xf64ull};
            top[-6] = m10;
            top[-5] = m7;
            top[-4] = m6;
            top[-3] = uint256_t{0xd78ull};
            top[-2] = m5;
            top[-1] = m4;
            top[0] = m3;
            top[1] = t2;
            top[2] = t1;
            top[3] = uint256_t{0xf02ull};
            top[4] = t1;
            top[5] = uint256_t{0x3f9ull};
            top[6] = t2;
            top[7] = m2;
            top += 7;
            MONAD_AOT_TAIL return b_1f66<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f02(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x90, 0x20, 0x90, 0x73, 0x9a, 0x8b, 0x8b, 0x51, 0x16, 0x91, 0x51, 0x92, 0x85, 0x51, 0x94, 0x85, 0x01, 0x95, 0x7f, 0x87, 0x52, 0x85, 0x01, 0x52, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x61, 0x81, 0x61, 0x56}, 12, 4));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x90, 0x20, 0x90, 0x73, 0x9a, 0x8b, 0x8b, 0x51, 0x16, 0x91, 0x51, 0x92, 0x85, 0x51, 0x94, 0x85, 0x01, 0x95, 0x7f, 0x87, 0x52, 0x85, 0x01, 0x52, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            auto const h3 = aot::sha3_any<traits>(ctx, gas, s1, t1);
            gas = ctx->gas_remaining;
            uint256_t const &s10 = top[-10];
            uint256_t const t2 = aot::mload<traits>(ctx, gas, s10);
            uint256_t const t3 = t2 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const &s4 = top[-4];
            uint256_t const t5 = aot::mload<traits>(ctx, gas, s4);
            uint256_t const &s3 = top[-3];
            uint256_t const t6 = t5 + s3;
            aot::mstore<traits>(ctx, gas, t6, uint256_t{0xa7f4d04f79440863ull, 0x4993c596f2fdd0aaull, 0xe68f0689007e325ull, 0xaf1b0d30d2cab038ull});
            uint256_t const t7 = t5 + s4;
            aot::mstore<traits>(ctx, gas, t7, h3);
            uint256_t const &s11 = top[-11];
            uint256_t const t8 = t5 + s11;
            aot::mstore<traits>(ctx, gas, t8, t3);
            uint256_t const t9 = t5 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t9, t4);
            aot::mstore<traits>(ctx, gas, t5, uint256_t{0x80ull});
            top[-11] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[-4] = t6;
            top[-3] = t5;
            top[-2] = uint256_t{0xd70ull};
            top[-1] = t5;
            top += -1;
            MONAD_AOT_TAIL return b_13ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f64(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x16, 0x90, 0x82, 0x51, 0x51, 0x92, 0x84}, 5, 1));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x16, 0x90, 0x82, 0x51, 0x51, 0x92, 0x84}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 & s1;
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const m3 = s3;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-3] = t4;
            top[-2] = t2;
            top[-1] = m2;
            top[0] = m3;
            top[1] = m4;
            top += 1;
            MONAD_AOT_TAIL return b_f6d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f6d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x81, 0x10, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::from_bool(s0 < s4);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_f78<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_f75<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f75(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x85, 0x80, 0xf3}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x85, 0x80, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            aot::finish(ctx, gas, StatusCode::Success, s5, s5);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f78(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x85, 0x85, 0x61, 0x60, 0x95, 0x87, 0x51, 0x61, 0x56}, 4, 8));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x85, 0x85, 0x61, 0x60, 0x95, 0x87, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[0] = uint256_t{0x1ull};
            top[1] = m0;
            top[2] = uint256_t{0xf91ull};
            top[3] = m3;
            top[4] = m2;
            top[5] = uint256_t{0xf8bull};
            top[6] = m0;
            top[7] = t1;
            top += 7;
            MONAD_AOT_TAIL return b_175e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f8b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x61, 0x56}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            top[0] = t1;
            MONAD_AOT_TAIL return b_199d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f91(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x01, 0x61, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            top[-1] = t1;
            top += -1;
            MONAD_AOT_TAIL return b_f6d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f97(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x61, 0x8e, 0x9f, 0x9e, 0x93, 0x61, 0x94, 0x51, 0x61, 0x56}, 13, 6));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x61, 0x8e, 0x9f, 0x9e, 0x93, 0x61, 0x94, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s11);
            uint256_t const m11 = s11;
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-12] = m11;
            top[-11] = m12;
            top[0] = uint256_t{0xfb2ull};
            top[1] = m0;
            top[2] = uint256_t{0x311ull};
            top[3] = uint256_t{0xfacull};
            top[4] = m0;
            top[5] = t1;
            top += 5;
            MONAD_AOT_TAIL return b_175e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fac(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x61, 0x56}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            top[0] = t1;
            MONAD_AOT_TAIL return b_1fbe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fb2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x9b, 0x9a, 0x9b, 0x61, 0x56}, 13, 1));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x9b, 0x9a, 0x9b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            top[-12] = m11;
            top[-11] = m12;
            MONAD_AOT_TAIL return b_ed9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fe9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x36, 0x03, 0x12, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x36, 0x03, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 - s1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x80ull}));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1046); }
            MONAD_AOT_TAIL return b_ff4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ff4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x85, 0x60, 0x91, 0x88, 0x51, 0x61, 0x81, 0x61, 0x56}, 7, 6));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x85, 0x60, 0x91, 0x88, 0x51, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s6);
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x80ull};
            top[1] = m5;
            top[2] = m0;
            top[3] = t1;
            top[4] = uint256_t{0x1002ull};
            top[5] = t1;
            top += 5;
            MONAD_AOT_TAIL return b_1398<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1002(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x85, 0x61, 0x56}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[1] = uint256_t{0x100bull};
            top[2] = m4;
            top += 2;
            MONAD_AOT_TAIL return b_1509<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_100b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x52, 0x61, 0x83, 0x86, 0x01, 0x61, 0x56}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x52, 0x61, 0x83, 0x86, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s1, s0);
            uint256_t const &s5 = top[-5];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s5 + s3;
            top[0] = uint256_t{0x1018ull};
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_1509<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1018(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x82, 0x01, 0x52, 0x61, 0x8a, 0x86, 0x01, 0x61, 0x56}, 11, 2));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x82, 0x01, 0x52, 0x61, 0x8a, 0x86, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s1 + s3;
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const &s5 = top[-5];
            uint256_t const &s10 = top[-10];
            uint256_t const t2 = s5 + s10;
            top[0] = uint256_t{0x1027ull};
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_1607<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1027(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x8a, 0x82, 0x01, 0x52, 0x8d, 0x61, 0x81, 0x87, 0x01, 0x61, 0x56}, 15, 3));
            if (MONAD_UNLIKELY(top - bottom < 15)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x8a, 0x82, 0x01, 0x52, 0x8d, 0x61, 0x81, 0x87, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s10 = top[-10];
            uint256_t const t1 = s1 + s10;
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const &s5 = top[-5];
            uint256_t const &s14 = top[-14];
            uint256_t const t2 = s5 + s14;
            uint256_t const m14 = s14;
            top[0] = m14;
            top[1] = uint256_t{0x1037ull};
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_1607<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1037(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x82, 0x01, 0x52, 0x81, 0x52, 0x01, 0x91, 0x01, 0x90, 0x61, 0x56}, 7, 1));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x82, 0x01, 0x52, 0x81, 0x52, 0x01, 0x91, 0x01, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s2 + s1;
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, s2);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = s3 + s4;
            uint256_t const &s6 = top[-6];
            uint256_t const &s5 = top[-5];
            uint256_t const t3 = s6 + s5;
            top[-6] = t3;
            top[-5] = t2;
            top += -5;
            MONAD_AOT_TAIL return b_e7a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1075(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x82, 0x34, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x82, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j5 = aot::nonzero(t1);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[0] = m3;
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x5bf); }
            MONAD_AOT_TAIL return b_107d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_107d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x140ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x5bf); }
            MONAD_AOT_TAIL return b_10a8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10a8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x36, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x36, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            top[1] = uint256_t{0x10b0ull};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_152a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_10b0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x80, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x80, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xffffffffffffff7cull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = aot::from_bool(slt(t2, s2));
            bool const j8 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[0] = m2;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x332); }
            MONAD_AOT_TAIL return b_10db<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10db(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x10e2ull};
            top += 1;
            MONAD_AOT_TAIL return b_1478<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_10e2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x93, 0x90, 0x61, 0x35, 0x85, 0x81, 0x11, 0x61, 0x57}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x93, 0x90, 0x61, 0x35, 0x85, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x104ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j10 = aot::nonzero(t2);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-3] = uint256_t{0xffffffffffffffffull};
            top[0] = m3;
            top[1] = m0;
            top[2] = t1;
            top += 2;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x49f); }
            MONAD_AOT_TAIL return b_10f9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10f9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x86, 0x01, 0x61, 0x56}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x86, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s4 = top[-4];
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s4 + s0;
            top[0] = uint256_t{0x1105ull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_15c1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1105(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x93, 0x61, 0x35, 0x96, 0x87, 0x11, 0x61, 0x57}, 7, 2));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x93, 0x61, 0x35, 0x96, 0x87, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x124ull});
            uint256_t const &s6 = top[-6];
            uint256_t const t2 = aot::from_bool(s6 < t1);
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-6] = t1;
            top[-4] = m1;
            top[-1] = m0;
            top[0] = m4;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x32a); }
            MONAD_AOT_TAIL return b_1113<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1113(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x96, 0x61, 0x98, 0x36, 0x91, 0x01, 0x61, 0x56}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x96, 0x61, 0x98, 0x36, 0x91, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s5 = top[-5];
            uint256_t const &s6 = top[-6];
            uint256_t const t2 = s5 + s6;
            top[-6] = uint256_t{0x2f6ull};
            top[-5] = uint256_t{0xbd1ull};
            top[1] = uint256_t{0x1125ull};
            top[2] = t1;
            top[3] = t2;
            top += 3;
            MONAD_AOT_TAIL return b_15c1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1125(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x96, 0x90, 0x95, 0x82, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 8, 4));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x96, 0x90, 0x95, 0x82, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-7] = m0;
            top[-6] = m1;
            top[-1] = m7;
            top[0] = t1;
            top[1] = m6;
            top[2] = uint256_t{0x1134ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_13ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1134(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x7f, 0x84, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x83, 0x51, 0x94, 0x85, 0x91, 0x81, 0x61, 0x60, 0x85, 0x01, 0x80, 0x96, 0x61, 0x56}, 5, 7));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x7f, 0x84, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x83, 0x51, 0x94, 0x85, 0x91, 0x81, 0x61, 0x60, 0x85, 0x01, 0x80, 0x96, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x64ull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x6d28546f6b656e50ull, 0x6e7366657246726full, 0x746e657373547261ull, 0x5065726d69745769ull});
            uint256_t const &s3 = top[-3];
            uint256_t const t2 = s1 + s3;
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x7265737320737065ull, 0x747465642c616464ull, 0x6e73207065726d69ull, 0x65726d697373696full});
            uint256_t const t3 = s1 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0x353620646561646cull, 0x63652c75696e7432ull, 0x74323536206e6f6eull, 0x6e6465722c75696eull});
            uint256_t const t4 = s1 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x696e652c00000000ull});
            uint256_t const t5 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const t6 = t5 + uint256_t{0x20ull};
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m1 = s1;
            top[-4] = t5;
            top[-1] = t6;
            top[0] = t5;
            top[1] = m4;
            top[2] = m0;
            top[3] = m4;
            top[4] = uint256_t{0x11e3ull};
            top[5] = t6;
            top[6] = m1;
            top += 6;
            MONAD_AOT_TAIL return b_1f93<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_11e3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x82, 0x37, 0x01, 0x8b, 0x81, 0x52, 0x03, 0x93, 0x61, 0x7f, 0x95, 0x86, 0x81, 0x01, 0x83, 0x52, 0x82, 0x61, 0x56}, 15, 1));
            if (MONAD_UNLIKELY(top - bottom < 15)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x82, 0x37, 0x01, 0x8b, 0x81, 0x52, 0x03, 0x93, 0x61, 0x7f, 0x95, 0x86, 0x81, 0x01, 0x83, 0x52, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const &s1 = top[-1];
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &s0, &s2, &s1);
            gas = ctx->gas_remaining;
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s0 + s3;
            uint256_t const &s14 = top[-14];
            aot::mstore<traits>(ctx, gas, t1, s14);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = t1 - s4;
            uint256_t const t3 = t2 + uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, s8, t3);
            uint256_t const m8 = s8;
            top[-8] = uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            top[-4] = m8;
            top[-3] = uint256_t{0x121cull};
            top[-2] = t2;
            top[-1] = m8;
            top += -1;
            MONAD_AOT_TAIL return b_1437<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_121c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x90, 0x20, 0x92, 0x61, 0x86, 0x51, 0x61, 0x56}, 7, 2));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x90, 0x20, 0x92, 0x61, 0x86, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            auto const h3 = aot::sha3_any<traits>(ctx, gas, s1, t1);
            gas = ctx->gas_remaining;
            uint256_t const &s6 = top[-6];
            uint256_t const t2 = aot::mload<traits>(ctx, gas, s6);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-4] = h3;
            top[-1] = m4;
            top[0] = uint256_t{0x122aull};
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_2054<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_122a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x87, 0x81, 0x01, 0x51, 0x85, 0x89, 0x01, 0x51, 0x95, 0x51, 0x91, 0x82, 0x01, 0x96, 0x87, 0x52, 0x60, 0x82, 0x01, 0x92, 0x90, 0x92, 0x52, 0x33, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x81, 0x01, 0x93, 0x90, 0x93, 0x52, 0x60, 0x35, 0x60, 0x84, 0x01, 0x52, 0x82, 0x60, 0x81, 0x01, 0x61, 0x56}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x87, 0x81, 0x01, 0x51, 0x85, 0x89, 0x01, 0x51, 0x95, 0x51, 0x91, 0x82, 0x01, 0x96, 0x87, 0x52, 0x60, 0x82, 0x01, 0x92, 0x90, 0x92, 0x52, 0x33, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x81, 0x01, 0x93, 0x90, 0x93, 0x52, 0x60, 0x35, 0x60, 0x84, 0x01, 0x52, 0x82, 0x60, 0x81, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = uint256_t{0x20ull} + s6;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = s6 + s3;
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const t5 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const t6 = t5 + uint256_t{0x20ull};
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, t6, s4);
            uint256_t const t7 = t5 + uint256_t{0x40ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t7, s0);
            uint256_t const t8 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t9 = t5 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t9, t8);
            uint256_t const t10 = t5 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t10, t2);
            uint256_t const t11 = t5 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t11, t4);
            uint256_t const t12 = aot::calldataload(ctx, uint256_t{0xe4ull});
            uint256_t const t13 = t5 + uint256_t{0xc0ull};
            aot::mstore<traits>(ctx, gas, t13, t12);
            uint256_t const t14 = t5 + uint256_t{0xe0ull};
            top[-4] = t6;
            top[-3] = t5;
            top[0] = t5;
            top[1] = t14;
            top += 1;
            MONAD_AOT_TAIL return b_2e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1274(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j7 = aot::nonzero(t3);
            top[1] = uint256_t{0x20ull};
            top += 1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x332); }
            MONAD_AOT_TAIL return b_129f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_129f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x35, 0x67, 0x92, 0x83, 0x82, 0x11, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x35, 0x67, 0x92, 0x83, 0x82, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::calldataload(ctx, s1);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j8 = aot::nonzero(t2);
            uint256_t const m1 = s1;
            top[-1] = uint256_t{0xffffffffffffffffull};
            top[1] = t1;
            top[2] = m1;
            top += 2;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xbda); }
            MONAD_AOT_TAIL return b_12b2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12b2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x36, 0x60, 0x83, 0x01, 0x12, 0x15, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x36, 0x60, 0x83, 0x01, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s1 + uint256_t{0x23ull};
            uint256_t const t3 = aot::from_bool(slt(t2, t1));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j7 = aot::nonzero(t4);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xbda); }
            MONAD_AOT_TAIL return b_12bd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12bd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x01, 0x35, 0x92, 0x83, 0x11, 0x61, 0x57}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x01, 0x35, 0x92, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 + s0;
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = aot::from_bool(s3 < t2);
            bool const j7 = aot::nonzero(t3);
            top[-3] = t2;
            top += -1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x32e); }
            MONAD_AOT_TAIL return b_12c7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12c7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x90, 0x60, 0x36, 0x83, 0x86, 0x83, 0x1b, 0x84, 0x01, 0x01, 0x11, 0x61, 0x57}, 3, 6));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x90, 0x60, 0x36, 0x83, 0x86, 0x83, 0x1b, 0x84, 0x01, 0x01, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = aot::shl_c<7>(s2);
            uint256_t const &s0 = top[0];
            uint256_t const t3 = s0 + t2;
            uint256_t const t4 = t3 + uint256_t{0x24ull};
            uint256_t const t5 = aot::from_bool(t1 < t4);
            bool const j13 = aot::nonzero(t5);
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x24ull};
            top[1] = m0;
            top[2] = uint256_t{0x7ull};
            top += 2;
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x49f); }
            MONAD_AOT_TAIL return b_12d9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12d9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x86}, 7, 1));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x86}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[1] = m6;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x12da);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12e2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x87, 0x80, 0xf3}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x87, 0x80, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            aot::finish(ctx, gas, StatusCode::Success, s7, s7);
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1318(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x88, 0x87, 0x60, 0x94, 0x60, 0x83, 0x51, 0x61, 0x81, 0x61, 0x56}, 8, 9));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x88, 0x87, 0x60, 0x94, 0x60, 0x83, 0x51, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s7);
            uint256_t const m7 = s7;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = uint256_t{0x1ull};
            top[1] = uint256_t{0x1392ull};
            top[2] = m7;
            top[3] = m5;
            top[4] = m1;
            top[5] = uint256_t{0x60ull};
            top[6] = t1;
            top[7] = uint256_t{0x132cull};
            top[8] = t1;
            top += 8;
            MONAD_AOT_TAIL return b_1398<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1398(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x80ull};
            uint256_t const t2 = aot::from_bool(t1 < s0);
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            uint256_t const t4 = t3 | t2;
            bool const j12 = aot::nonzero(t4);
            top[0] = t1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x13b4); }
            MONAD_AOT_TAIL return b_13b0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_13b0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_13e3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x60ull};
            uint256_t const t2 = aot::from_bool(t1 < s0);
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            uint256_t const t4 = t3 | t2;
            bool const j12 = aot::nonzero(t4);
            top[0] = t1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x13b4); }
            MONAD_AOT_TAIL return b_13fb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_13fb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_13ff(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0xa0ull};
            uint256_t const t2 = aot::from_bool(t1 < s0);
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            uint256_t const t4 = t3 | t2;
            bool const j12 = aot::nonzero(t4);
            top[0] = t1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x13b4); }
            MONAD_AOT_TAIL return b_1417<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1417(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_141b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0xc0ull};
            uint256_t const t2 = aot::from_bool(t1 < s0);
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            uint256_t const t4 = t3 | t2;
            bool const j12 = aot::nonzero(t4);
            top[0] = t1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x13b4); }
            MONAD_AOT_TAIL return b_1433<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1433(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1437(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x60, 0x7f, 0x91, 0x01, 0x16, 0x81, 0x01, 0x90, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x60, 0x7f, 0x91, 0x01, 0x16, 0x81, 0x01, 0x90, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x1full};
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s0 = top[0];
            uint256_t const t3 = s0 + t2;
            uint256_t const t4 = aot::from_bool(t3 < s0);
            uint256_t const t5 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t3);
            uint256_t const t6 = t5 | t4;
            bool const j17 = aot::nonzero(t6);
            top[-1] = t3;
            top += -1;
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x13b4); }
            MONAD_AOT_TAIL return b_1474<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1474(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1478(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x90, 0x73, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x90, 0x73, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xc4ull});
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = t1 - t2;
            bool const j10 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_149a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_149a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_14a0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x90, 0x73, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x90, 0x73, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = t1 - t2;
            bool const j10 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_14c2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14c2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_14c3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x90, 0x73, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x90, 0x73, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = t1 - t2;
            bool const j10 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_14e5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14e5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_14e6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x90, 0x73, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x90, 0x73, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = t1 - t2;
            bool const j10 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_1508<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1508(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1509(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x35, 0x90, 0x73, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x35, 0x90, 0x73, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = t1 - t2;
            bool const j9 = aot::nonzero(t3);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[0] = m1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_1529<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1529(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_152a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x01, 0x90, 0x60, 0x82, 0x12, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x01, 0x90, 0x60, 0x82, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + s0;
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x80ull}));
            bool const j8 = aot::nonzero(t2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[0] = m1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_1556<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1556(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            top[1] = t1;
            top[2] = uint256_t{0x40ull};
            top[3] = uint256_t{0x1563ull};
            top[4] = t1;
            top += 4;
            MONAD_AOT_TAIL return b_13e3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1563(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x82, 0x94, 0x12, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x82, 0x94, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(slt(s3, s0));
            bool const j6 = aot::nonzero(t1);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-3] = m1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_156c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_156c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x51, 0x81, 0x81, 0x01, 0x81, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x51, 0x81, 0x81, 0x01, 0x81, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = t1 + s0;
            uint256_t const t3 = aot::from_bool(t2 < t1);
            uint256_t const t4 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t2);
            uint256_t const t5 = t4 | t3;
            bool const j13 = aot::nonzero(t5);
            top[1] = t1;
            top[2] = t2;
            top += 2;
            if (j13) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x13b4); }
            MONAD_AOT_TAIL return b_1584<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1584(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x52, 0x60, 0x35, 0x73, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x52, 0x60, 0x35, 0x73, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s2, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = t1 - t2;
            bool const j10 = aot::nonzero(t3);
            top[0] = t1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_15a6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_15a6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x52, 0x60, 0x35, 0x60, 0x82, 0x01, 0x52, 0x82, 0x52, 0x60, 0x35, 0x60, 0x83, 0x01, 0x52, 0x60, 0x35, 0x91, 0x01, 0x52, 0x56}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x52, 0x60, 0x35, 0x60, 0x82, 0x01, 0x52, 0x82, 0x52, 0x60, 0x35, 0x60, 0x83, 0x01, 0x52, 0x60, 0x35, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s1, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t2, t1);
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, s1);
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t4 = s3 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const t5 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const &s2 = top[-2];
            uint256_t const t6 = s3 + s2;
            aot::mstore<traits>(ctx, gas, t6, t5);
            uint256_t const &s4 = top[-4];
            uint64_t const jt = aot::jump_offset(s4);
            top += -5;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_15c1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_15ce<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_15ce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_15e0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_15e0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_15ee<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_15ee(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_15ef(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x81, 0x11, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xffffffffffffffffull} < s0);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x13b4); }
            MONAD_AOT_TAIL return b_15ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_15ff(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1607(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x35, 0x90, 0x65, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x35, 0x90, 0x65, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffull};
            uint256_t const t3 = t1 - t2;
            bool const j9 = aot::nonzero(t3);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[0] = m1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_1619<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1619(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_161a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_1627<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1627(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_1639<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1639(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0x85, 0x01, 0x94, 0x84, 0x60, 0x1b, 0x01, 0x01, 0x11, 0x61, 0x57}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0x85, 0x01, 0x94, 0x84, 0x60, 0x1b, 0x01, 0x01, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x20ull};
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = aot::shl_c<6>(s2);
            uint256_t const t3 = t2 + s3;
            uint256_t const t4 = t3 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            uint256_t const t5 = aot::from_bool(s0 < t4);
            bool const j12 = aot::nonzero(t5);
            top[-3] = t1;
            top += -1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_164a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_164a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_164b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_1659<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1659(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0x51, 0x91, 0x61, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = uint256_t{0x40ull};
            top[2] = m0;
            top[3] = uint256_t{0x1666ull};
            top[4] = t1;
            top += 4;
            MONAD_AOT_TAIL return b_13e3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1666(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x94, 0x81, 0x35, 0x67, 0x90, 0x81, 0x81, 0x11, 0x61, 0x57}, 5, 5));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x94, 0x81, 0x35, 0x67, 0x90, 0x81, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j11 = aot::nonzero(t2);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-4] = m2;
            top[1] = m4;
            top[2] = uint256_t{0xffffffffffffffffull};
            top[3] = t1;
            top += 3;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_167c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_167c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x83, 0x01, 0x82, 0x60, 0x82, 0x01, 0x12, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x83, 0x01, 0x82, 0x60, 0x82, 0x01, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s3 + s0;
            uint256_t const t2 = t1 + uint256_t{0x1full};
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = aot::from_bool(slt(t2, s2));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j9 = aot::nonzero(t4);
            top[0] = t1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_1689<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1689(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x35, 0x61, 0x81, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x35, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            top[1] = t1;
            top[2] = uint256_t{0x1693ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_15ef<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1693(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x61, 0x87, 0x51, 0x94, 0x85, 0x61, 0x56}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x61, 0x87, 0x51, 0x94, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s6);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-3] = t1;
            top[0] = m3;
            top[1] = uint256_t{0x16a0ull};
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_1437<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_16a0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x84, 0x52, 0x60, 0x94, 0x85, 0x80, 0x86, 0x01, 0x93, 0x60, 0x1b, 0x85, 0x01, 0x01, 0x93, 0x81, 0x85, 0x11, 0x61, 0x57}, 5, 4));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x84, 0x52, 0x60, 0x94, 0x85, 0x80, 0x86, 0x01, 0x93, 0x60, 0x1b, 0x85, 0x01, 0x01, 0x93, 0x81, 0x85, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s3, s1);
            uint256_t const t1 = s3 + uint256_t{0x20ull};
            uint256_t const t2 = aot::shl_c<6>(s1);
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = s2 + t2;
            uint256_t const t4 = t3 + uint256_t{0x20ull};
            uint256_t const &s4 = top[-4];
            uint256_t const t5 = aot::from_bool(s4 < t4);
            bool const j21 = aot::nonzero(t5);
            uint256_t const m4 = s4;
            uint256_t const m2 = s2;
            top[-4] = uint256_t{0x20ull};
            top[-2] = t4;
            top[-1] = t1;
            top[1] = m4;
            top[2] = m2;
            top += 2;
            if (j21) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_16ba<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_16ba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x86, 0x89, 0x98, 0x97, 0x96, 0x95, 0x94, 0x93, 0x92, 0x01, 0x92}, 9, 2));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x86, 0x89, 0x98, 0x97, 0x96, 0x95, 0x94, 0x93, 0x92, 0x01, 0x92}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s0 + s6;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-7] = m8;
            top[-6] = m7;
            top[-5] = m6;
            top[-4] = m5;
            top[-3] = m4;
            top[-2] = t1;
            top[-1] = m2;
            top[0] = m1;
            top[1] = m3;
            top += 1;
            MONAD_AOT_TAIL return b_16c6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_16c6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x84, 0x10, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x84, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::from_bool(s3 < s4);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_16e3<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_16ce<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_16ce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x85, 0x52, 0x80, 0x82, 0x01, 0x35, 0x90, 0x85, 0x01, 0x52, 0x01, 0x35, 0x91, 0x01, 0x52, 0x56}, 12, 0));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x85, 0x52, 0x80, 0x82, 0x01, 0x35, 0x90, 0x85, 0x01, 0x52, 0x01, 0x35, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s10 = top[-10];
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, s10, s5);
            uint256_t const &s7 = top[-7];
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s7 + s6;
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const t3 = s10 + s6;
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const &s8 = top[-8];
            uint256_t const t4 = s7 + s8;
            uint256_t const t5 = aot::calldataload(ctx, t4);
            uint256_t const &s9 = top[-9];
            uint256_t const t6 = s10 + s9;
            aot::mstore<traits>(ctx, gas, t6, t5);
            uint256_t const &s11 = top[-11];
            uint64_t const jt = aot::jump_offset(s11);
            top += -12;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_16e3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x84, 0x83, 0x03, 0x12, 0x61, 0x57}, 9, 2));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x84, 0x83, 0x03, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s1 - s3;
            uint256_t const &s8 = top[-8];
            uint256_t const t2 = aot::from_bool(slt(t1, s8));
            bool const j14 = aot::nonzero(t2);
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-8] = m7;
            top[-7] = m6;
            top[-6] = m5;
            top[-5] = m4;
            top[-4] = m3;
            top[-3] = m2;
            top[-2] = m1;
            top[-1] = m0;
            top += -1;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_16f4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_16f4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x88, 0x51, 0x90, 0x89, 0x82, 0x01, 0x90, 0x82, 0x82, 0x10, 0x85, 0x83, 0x11, 0x17, 0x61, 0x57}, 9, 5));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x88, 0x51, 0x90, 0x89, 0x82, 0x01, 0x90, 0x82, 0x82, 0x10, 0x85, 0x83, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s8);
            uint256_t const t2 = t1 + s8;
            uint256_t const t3 = aot::from_bool(t2 < t1);
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = aot::from_bool(s2 < t2);
            uint256_t const t5 = t4 | t3;
            bool const j15 = aot::nonzero(t5);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = t2;
            top[2] = m0;
            top += 2;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1730); }
            MONAD_AOT_TAIL return b_1706<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1706(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x8a, 0x92, 0x89, 0x92, 0x84, 0x52, 0x61, 0x87, 0x61, 0x56}, 11, 4));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x8a, 0x92, 0x89, 0x92, 0x84, 0x52, 0x61, 0x87, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s10 = top[-10];
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s10, s1);
            uint256_t const m10 = s10;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-2] = m10;
            top[-1] = m8;
            top[1] = m2;
            top[2] = uint256_t{0x1714ull};
            top[3] = m5;
            top += 3;
            MONAD_AOT_TAIL return b_1509<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1714(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x52, 0x82, 0x87, 0x01, 0x35, 0x83, 0x82, 0x01, 0x52, 0x81, 0x52, 0x01, 0x93, 0x01, 0x91, 0x90, 0x88, 0x97, 0x96, 0x95, 0x94, 0x93, 0x61, 0x56}, 13, 2));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x52, 0x82, 0x87, 0x01, 0x35, 0x83, 0x82, 0x01, 0x52, 0x81, 0x52, 0x01, 0x93, 0x01, 0x91, 0x90, 0x88, 0x97, 0x96, 0x95, 0x94, 0x93, 0x61, 0x56}) + 0;
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
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-11] = m12;
            top[-10] = m11;
            top[-9] = m10;
            top[-8] = m9;
            top[-7] = m8;
            top[-6] = t5;
            top[-5] = m6;
            top[-4] = m5;
            top[-3] = t4;
            top += -3;
            MONAD_AOT_TAIL return b_16c6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_175e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1772); }
            MONAD_AOT_TAIL return b_1768<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1768(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_17a1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x91, 0x92, 0x73, 0x60, 0x60, 0x82, 0x84, 0x16, 0x81, 0x52, 0x60, 0x60, 0x52, 0x82, 0x82, 0x82, 0x20, 0x96, 0x16, 0x95, 0x86, 0x82, 0x52, 0x60, 0x52, 0x81, 0x81, 0x20, 0x33, 0x82, 0x52, 0x60, 0x52, 0x20, 0x94, 0x85, 0x54, 0x95, 0x65, 0x87, 0x60, 0x1c, 0x16, 0x80, 0x42, 0x11, 0x61, 0x57}, 4, 6));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x91, 0x92, 0x73, 0x60, 0x60, 0x82, 0x84, 0x16, 0x81, 0x52, 0x60, 0x60, 0x52, 0x82, 0x82, 0x82, 0x20, 0x96, 0x16, 0x95, 0x86, 0x82, 0x52, 0x60, 0x52, 0x81, 0x81, 0x20, 0x33, 0x82, 0x52, 0x60, 0x52, 0x20, 0x94, 0x85, 0x54, 0x95, 0x65, 0x87, 0x60, 0x1c, 0x16, 0x80, 0x42, 0x11, 0x61, 0x57}) + 36;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x1ull});
            uint256_t const t2 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = s3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t2);
            uint256_t const t4 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t5 = runtime::uint256_from_address(ctx->env.sender);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t5);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t4);
            uint256_t const t6 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t7 = aot::sload<traits>(ctx, gas, t6);
            uint256_t const t8 = aot::shr_c<160>(t7);
            uint256_t const t9 = t8 & uint256_t{0xffffffffffffull};
            uint256_t const t10 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const t11 = aot::from_bool(t9 < t10);
            bool const j49 = aot::nonzero(t11);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-3] = t7;
            top[-2] = t3;
            top[1] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[2] = m2;
            top[3] = t6;
            top[4] = t9;
            top += 4;
            if (j49) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1884); }
            MONAD_AOT_TAIL return b_17f6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_17f6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x82, 0x87, 0x16, 0x96, 0x83, 0x88, 0x03, 0x61, 0x57}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x82, 0x87, 0x16, 0x96, 0x83, 0x88, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s7 & s3;
            uint256_t const t2 = t1 - s3;
            bool const j9 = aot::nonzero(t2);
            uint256_t const m7 = s7;
            top[-7] = t1;
            top[0] = m7;
            if (j9) { MONAD_AOT_TAIL return b_1812<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1802<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1802(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x61, 0x95, 0x50, 0x16, 0x92, 0x61, 0x56}, 8, 0));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x61, 0x95, 0x50, 0x16, 0x92, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s2 & s3;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-7] = uint256_t{0x1810ull};
            top[-6] = t1;
            top[-3] = m6;
            top += -3;
            MONAD_AOT_TAIL return b_18b5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1810(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
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
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x87, 0x84, 0x84, 0x16, 0x11, 0x60, 0x14, 0x61, 0x57}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x87, 0x84, 0x84, 0x16, 0x11, 0x60, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s2 & s3;
            uint256_t const &s7 = top[-7];
            uint256_t const t2 = aot::from_bool(s7 < t1);
            uint256_t const t3 = aot::from_bool(uint256_t{0x0ull} == t2);
            bool const j9 = aot::nonzero(t3);
            if (j9) { MONAD_AOT_TAIL return b_184f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_181f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_181f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x88, 0x60, 0x51, 0x90, 0x7f, 0x82, 0x52, 0x60, 0x82, 0x01, 0x52, 0xfd}, 8, 5));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x88, 0x60, 0x51, 0x90, 0x7f, 0x82, 0x52, 0x60, 0x82, 0x01, 0x52, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xf96fb07100000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const &s7 = top[-7];
            aot::mstore<traits>(ctx, gas, t2, s7);
            aot::finish(ctx, gas, StatusCode::Revert, t1, uint256_t{0x24ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_184f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x84, 0x84, 0x61, 0x9a, 0x03, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x38, 0x80, 0x61, 0x56}, 8, 4));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x84, 0x84, 0x61, 0x9a, 0x03, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x38, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s7 - s2;
            uint256_t const &s3 = top[-3];
            uint256_t const t2 = t1 & s3;
            uint256_t const &s0 = top[0];
            uint256_t const t3 = s0 & uint256_t{0x0ull, 0x0ull, 0xffffffff00000000ull, 0xffffffffffffffffull};
            uint256_t const t4 = t3 | t2;
            uint256_t const &s1 = top[-1];
            aot::sstore<traits>(ctx, gas, s1, t4, (aot::gas_of<traits>({0x38, 0x80, 0x61, 0x56}) + 0));
            top[-7] = uint256_t{0x1810ull};
            top[-1] = uint256_t{0x23c0ull};
            top[0] = uint256_t{0x23c0ull};
            MONAD_AOT_TAIL return b_1802<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_18b5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x60, 0x60, 0x92, 0x60, 0x95, 0x82, 0x95, 0x60, 0x51, 0x94, 0x7f, 0x86, 0x52, 0x60, 0x86, 0x01, 0x52, 0x60, 0x85, 0x01, 0x52, 0x60, 0x84, 0x01, 0x52, 0x5a, 0xf1, 0x3d, 0x15, 0x60, 0x3d, 0x11, 0x60, 0x60, 0x51, 0x14, 0x16, 0x17, 0x16, 0x15, 0x61, 0x57}, 4, 7));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x60, 0x60, 0x92, 0x60, 0x95, 0x82, 0x95, 0x60, 0x51, 0x94, 0x7f, 0x86, 0x52, 0x60, 0x86, 0x01, 0x52, 0x60, 0x85, 0x01, 0x52, 0x60, 0x84, 0x01, 0x52, 0x5a, 0xf1, 0x3d, 0x15, 0x60, 0x3d, 0x11, 0x60, 0x60, 0x51, 0x14, 0x16, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x23b872dd00000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t2, s1);
            uint256_t const t3 = t1 + uint256_t{0x24ull};
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t3, s2);
            uint256_t const t4 = t1 + uint256_t{0x44ull};
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, t4, s3);
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xf1, 0x3d, 0x15, 0x60, 0x3d, 0x11, 0x60, 0x60, 0x51, 0x14, 0x16, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const &s0 = top[0];
            auto const c28 = aot::call<traits>(ctx, gas, t5, s0, uint256_t{0x0ull}, t1, uint256_t{0x64ull}, uint256_t{0x0ull}, uint256_t{0x20ull}, (aot::gas_of<traits>({0x3d, 0x15, 0x60, 0x3d, 0x11, 0x60, 0x60, 0x51, 0x14, 0x16, 0x17, 0x16, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t6 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t9 = aot::from_bool(uint256_t{0x1full} < t8);
            uint256_t const t10 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const t11 = aot::from_bool(t10 == uint256_t{0x1ull});
            uint256_t const t12 = t11 & t9;
            uint256_t const t13 = t12 | t7;
            uint256_t const t14 = t13 & c28;
            uint256_t const t15 = aot::from_bool(!aot::nonzero(t14));
            bool const j43 = aot::nonzero(t15);
            top += -4;
            if (j43) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x190e); }
            MONAD_AOT_TAIL return b_190d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_190d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_196c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1772); }
            MONAD_AOT_TAIL return b_1976<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1976(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1b, 0x01, 0x90, 0x56}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1b, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<6>(s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 + s1;
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t2;
            top += -2;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_197c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x35, 0x73, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x35, 0x73, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = t1 - t2;
            bool const j8 = aot::nonzero(t3);
            top[0] = t1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_199b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_199b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_199d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x65, 0x90, 0x81, 0x60, 0x84, 0x01, 0x51, 0x16, 0x73, 0x90, 0x81, 0x85, 0x51, 0x16, 0x94, 0x82, 0x60, 0x82, 0x01, 0x51, 0x16, 0x92, 0x80, 0x86, 0x60, 0x80, 0x94, 0x01, 0x51, 0x16, 0x95, 0x16, 0x95, 0x60, 0x91, 0x87, 0x83, 0x52, 0x60, 0x60, 0x52, 0x83, 0x83, 0x20, 0x89, 0x84, 0x52, 0x60, 0x52, 0x83, 0x83, 0x20, 0x99, 0x16, 0x98, 0x89, 0x83, 0x52, 0x60, 0x52, 0x82, 0x82, 0x20, 0x91, 0x84, 0x83, 0x54, 0x60, 0x1c, 0x03, 0x61, 0x57}, 3, 10));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x65, 0x90, 0x81, 0x60, 0x84, 0x01, 0x51, 0x16, 0x73, 0x90, 0x81, 0x85, 0x51, 0x16, 0x94, 0x82, 0x60, 0x82, 0x01, 0x51, 0x16, 0x92, 0x80, 0x86, 0x60, 0x80, 0x94, 0x01, 0x51, 0x16, 0x95, 0x16, 0x95, 0x60, 0x91, 0x87, 0x83, 0x52, 0x60, 0x60, 0x52, 0x83, 0x83, 0x20, 0x89, 0x84, 0x52, 0x60, 0x52, 0x83, 0x83, 0x20, 0x99, 0x16, 0x98, 0x89, 0x83, 0x52, 0x60, 0x52, 0x82, 0x82, 0x20, 0x91, 0x84, 0x83, 0x54, 0x60, 0x1c, 0x03, 0x61, 0x57}) + 36;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x60ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = t2 & uint256_t{0xffffffffffffull};
            uint256_t const t4 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t5 = t4 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t6 = s0 + uint256_t{0x20ull};
            uint256_t const t7 = aot::mload<traits>(ctx, gas, t6);
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t9 = s0 + uint256_t{0x40ull};
            uint256_t const t10 = aot::mload<traits>(ctx, gas, t9);
            uint256_t const t11 = t10 & uint256_t{0xffffffffffffull};
            uint256_t const &s1 = top[-1];
            uint256_t const t12 = s1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t12);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x1ull});
            uint256_t const t13 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t5);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t13);
            uint256_t const t14 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const &s2 = top[-2];
            uint256_t const t15 = s2 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t15);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t14);
            uint256_t const t16 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t17 = aot::sload<traits>(ctx, gas, t16);
            uint256_t const t18 = aot::shr_c<208>(t17);
            uint256_t const t19 = t18 - t3;
            bool const j73 = aot::nonzero(t19);
            top[-2] = t15;
            top[-1] = t5;
            top[0] = t12;
            top[1] = t11;
            top[2] = t8;
            top[3] = t3;
            top[4] = uint256_t{0x40ull};
            top[5] = t16;
            top[6] = uint256_t{0xffffffffffffull};
            top[7] = uint256_t{0x0ull};
            top += 7;
            if (j73) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1af5); }
            MONAD_AOT_TAIL return b_1a0c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a0c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x91, 0x85, 0x61, 0x94, 0x92, 0x7f, 0x98, 0x97, 0x96, 0x94, 0x50, 0x87, 0x15, 0x60, 0x14, 0x61, 0x57}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x91, 0x85, 0x61, 0x94, 0x92, 0x7f, 0x98, 0x97, 0x96, 0x94, 0x50, 0x87, 0x15, 0x60, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s6));
            uint256_t const t2 = aot::from_bool(uint256_t{0x0ull} == t1);
            bool const j16 = aot::nonzero(t2);
            uint256_t const m6 = s6;
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
            top[-6] = uint256_t{0x23e81d1bdb9708ecull, 0x16b817020812c732ull, 0x24a8ac08eef205beull, 0xc6a377bfc4eb1200ull};
            top[-5] = m6;
            top[-4] = m5;
            top[-3] = uint256_t{0x1aceull};
            top[-2] = m4;
            top[-1] = m3;
            top[0] = m2;
            top[1] = m5;
            top[2] = m1;
            top += 2;
            if (j16) { MONAD_AOT_TAIL return b_1ad3<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1a42<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a42(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x79, 0x90, 0x42, 0x16}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x79, 0x90, 0x42, 0x16}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = t1 & s0;
            top[0] = uint256_t{0x0ull, 0x0ull, 0xffffffff00000000ull, 0xffffull};
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_1a60<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a60(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x1b, 0x16, 0x7f, 0x60, 0x86, 0x01, 0x60, 0x1b, 0x16, 0x17, 0x17, 0x90, 0x55, 0x51, 0x93, 0x84, 0x93, 0x84, 0x91, 0x60, 0x91, 0x94, 0x93, 0x73, 0x60, 0x85, 0x01, 0x96, 0x16, 0x84, 0x52, 0x65, 0x80, 0x92, 0x16, 0x60, 0x85, 0x01, 0x52, 0x16, 0x91, 0x01, 0x52, 0x56}, 9, 2));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x1b, 0x16, 0x7f, 0x60, 0x86, 0x01, 0x60, 0x1b, 0x16, 0x17, 0x17, 0x90, 0x55, 0x51, 0x93, 0x84, 0x93, 0x84, 0x91, 0x60, 0x91, 0x94, 0x93, 0x73, 0x60, 0x85, 0x01, 0x96, 0x16, 0x84, 0x52, 0x65, 0x80, 0x92, 0x16, 0x60, 0x85, 0x01, 0x52, 0x16, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<160>(s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 & s1;
            uint256_t const &s5 = top[-5];
            uint256_t const t3 = s5 + uint256_t{0x1ull};
            uint256_t const t4 = aot::shl_c<208>(t3);
            uint256_t const t5 = t4 & uint256_t{0x0ull, 0x0ull, 0x0ull, 0xffffffffffff0000ull};
            uint256_t const t6 = t5 | t2;
            uint256_t const &s2 = top[-2];
            uint256_t const t7 = t6 | s2;
            uint256_t const &s3 = top[-3];
            aot::sstore<traits>(ctx, gas, s3, t7, (aot::gas_of<traits>({0x51, 0x93, 0x84, 0x93, 0x84, 0x91, 0x60, 0x91, 0x94, 0x93, 0x73, 0x60, 0x85, 0x01, 0x96, 0x16, 0x84, 0x52, 0x65, 0x80, 0x92, 0x16, 0x60, 0x85, 0x01, 0x52, 0x16, 0x91, 0x01, 0x52, 0x56}) + 0));
            uint256_t const &s4 = top[-4];
            uint256_t const t8 = aot::mload<traits>(ctx, gas, s4);
            uint256_t const t9 = t8 + uint256_t{0x60ull};
            uint256_t const &s7 = top[-7];
            uint256_t const t10 = s7 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore<traits>(ctx, gas, t8, t10);
            uint256_t const &s8 = top[-8];
            uint256_t const t11 = s8 & uint256_t{0xffffffffffffull};
            uint256_t const t12 = t8 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t12, t11);
            uint256_t const t13 = s5 & uint256_t{0xffffffffffffull};
            uint256_t const t14 = t8 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t14, t13);
            uint256_t const &s6 = top[-6];
            uint64_t const jt = aot::jump_offset(s6);
            top[-8] = t8;
            top[-7] = t8;
            top[-6] = t9;
            top += -6;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ace(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x03, 0x90, 0xa4, 0x56}, 8, 0));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x03, 0x90, 0xa4, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            uint256_t const &s4 = top[-4];
            uint256_t const &s5 = top[-5];
            uint256_t const &s6 = top[-6];
            ctx->gas_remaining = gas;
            runtime::log4<traits>(ctx, &s2, &t1, &s3, &s4, &s5, &s6);
            gas = ctx->gas_remaining;
            uint256_t const &s7 = top[-7];
            uint64_t const jt = aot::jump_offset(s7);
            top += -8;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ad3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x79, 0x87, 0x61, 0x56}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x79, 0x87, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[0] = uint256_t{0x0ull, 0x0ull, 0xffffffff00000000ull, 0xffffull};
            top[1] = m7;
            top += 1;
            MONAD_AOT_TAIL return b_1a60<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1b1e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x46, 0x7f, 0x03, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x46, 0x7f, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.tx_context->chain_id);
            uint256_t const t2 = uint256_t{0x1ull} - t1;
            bool const j5 = aot::nonzero(t2);
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b69); }
            MONAD_AOT_TAIL return b_1b46<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b46(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x90, 0x56}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top[0] = uint256_t{0x7cc04ff903e3f28ull, 0x913915c28be3b9aaull, 0x5d6c7ab78eb2b2fcull, 0x866a5aba21966af9ull};
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1bd3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1bd9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x1be1ull};
            top += 1;
            MONAD_AOT_TAIL return b_1b1e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1be1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x60, 0x51, 0x90, 0x60, 0x82, 0x01, 0x92, 0x7f, 0x84, 0x52, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x61, 0x81, 0x61, 0x56}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x60, 0x51, 0x90, 0x60, 0x82, 0x01, 0x92, 0x7f, 0x84, 0x52, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x1901000000000000ull});
            uint256_t const t3 = t1 + uint256_t{0x22ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t3, s0);
            uint256_t const t4 = t1 + uint256_t{0x42ull};
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t4, s1);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x42ull});
            top[-1] = t2;
            top[0] = t1;
            top[1] = uint256_t{0x1bd3ull};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_1398<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1c25(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x92, 0x90, 0x93, 0x60, 0x35, 0x93, 0x60, 0x84, 0x01, 0x51, 0x80, 0x42, 0x11, 0x61, 0x57}, 5, 4));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x92, 0x90, 0x93, 0x60, 0x35, 0x93, 0x60, 0x84, 0x01, 0x51, 0x80, 0x42, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 + uint256_t{0x40ull};
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const t5 = aot::from_bool(t3 < t4);
            bool const j16 = aot::nonzero(t5);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const m0 = s0;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-4] = m1;
            top[-3] = t1;
            top[-2] = m0;
            top[-1] = m3;
            top[0] = m4;
            top[1] = m2;
            top[2] = t3;
            top += 2;
            if (j16) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1cc6); }
            MONAD_AOT_TAIL return b_1c3a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c3a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x60, 0x84, 0x51, 0x01, 0x51, 0x80, 0x86, 0x11, 0x61, 0x57}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x60, 0x84, 0x51, 0x01, 0x51, 0x80, 0x86, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s4);
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const &s5 = top[-5];
            uint256_t const t4 = aot::from_bool(t3 < s5);
            bool const j10 = aot::nonzero(t4);
            top[0] = t3;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1c95); }
            MONAD_AOT_TAIL return b_1c48<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c48(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x91, 0x85, 0x91, 0x61, 0x61, 0x94, 0x61, 0x60, 0x88, 0x01, 0x51, 0x86, 0x61, 0x56}, 7, 6));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x91, 0x85, 0x91, 0x61, 0x61, 0x94, 0x61, 0x60, 0x88, 0x01, 0x51, 0x86, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s4 + uint256_t{0x20ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-3] = uint256_t{0x1c65ull};
            top[-2] = m6;
            top[-1] = m3;
            top[0] = m2;
            top[1] = uint256_t{0xd78ull};
            top[2] = m1;
            top[3] = uint256_t{0x1c60ull};
            top[4] = t2;
            top[5] = m6;
            top += 5;
            MONAD_AOT_TAIL return b_1e47<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1c60(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_1bd9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1c65(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x80, 0x91, 0x51, 0x51, 0x16, 0x92, 0x60, 0x35, 0x91, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x80, 0x91, 0x51, 0x51, 0x16, 0x92, 0x60, 0x35, 0x91, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = t2 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t4 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t5 = t4 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t6 = t4 - t5;
            bool const j16 = aot::nonzero(t6);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t3;
            top[0] = t4;
            top[1] = m2;
            top += 1;
            if (j16) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_1c8d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c8d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x93, 0x61, 0x56}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x93, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = uint256_t{0x1810ull};
            top[1] = m3;
            top += 1;
            MONAD_AOT_TAIL return b_18b5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1cf7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x95, 0x90, 0x93, 0x95, 0x80, 0x51, 0x51, 0x95, 0x60, 0x92, 0x83, 0x83, 0x01, 0x51, 0x80, 0x42, 0x11, 0x61, 0x57}, 7, 5));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x95, 0x90, 0x93, 0x95, 0x80, 0x51, 0x51, 0x95, 0x60, 0x92, 0x83, 0x83, 0x01, 0x51, 0x80, 0x42, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = s0 + uint256_t{0x40ull};
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const t6 = aot::from_bool(t4 < t5);
            bool const j19 = aot::nonzero(t6);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-6] = m4;
            top[-5] = t2;
            top[-4] = m1;
            top[-1] = uint256_t{0x40ull};
            top[1] = m5;
            top[2] = m6;
            top[3] = t4;
            top += 3;
            if (j19) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1e17); }
            MONAD_AOT_TAIL return b_1d0e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d0e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x84, 0x88, 0x03, 0x61, 0x57}, 9, 1));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x84, 0x88, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = s8 - s5;
            bool const j5 = aot::nonzero(t1);
            top += -1;
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1dee); }
            MONAD_AOT_TAIL return b_1d16<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d16(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x91, 0x86, 0x91, 0x61, 0x60, 0x9b, 0x61, 0x8d, 0x88, 0x01, 0x51, 0x86, 0x61, 0x56}, 9, 8));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x91, 0x86, 0x91, 0x61, 0x60, 0x9b, 0x61, 0x8d, 0x88, 0x01, 0x51, 0x86, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0x20ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-8] = uint256_t{0x20ull};
            top[-1] = uint256_t{0x1d2eull};
            top[0] = m5;
            top[1] = m1;
            top[2] = m0;
            top[3] = uint256_t{0xd78ull};
            top[4] = m8;
            top[5] = uint256_t{0x1c60ull};
            top[6] = t2;
            top[7] = m5;
            top += 7;
            MONAD_AOT_TAIL return b_1e47<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d2e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_1d31<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d31(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x86, 0x81, 0x10, 0x61, 0x57}, 7, 2));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x86, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::from_bool(s0 < s6);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1d42<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1d39<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d39(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}, 9, 0));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint64_t const jt = aot::jump_offset(s8);
            top += -9;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d42(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x83, 0x51, 0x61, 0x56}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x83, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x1d4dull};
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_175e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d4d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x88, 0x61, 0x83, 0x87, 0x8a, 0x61, 0x56}, 9, 6));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x88, 0x61, 0x83, 0x87, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[0] = t1;
            top[1] = m8;
            top[2] = uint256_t{0x1d5aull};
            top[3] = m1;
            top[4] = m4;
            top[5] = m6;
            top += 5;
            MONAD_AOT_TAIL return b_196c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d5a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x01, 0x35, 0x90, 0x89, 0x81, 0x01, 0x51, 0x80, 0x83, 0x11, 0x61, 0x57}, 11, 2));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x01, 0x35, 0x90, 0x89, 0x81, 0x01, 0x51, 0x80, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const &s2 = top[-2];
            uint256_t const &s10 = top[-10];
            uint256_t const t3 = s2 + s10;
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const t5 = aot::from_bool(t4 < t2);
            bool const j12 = aot::nonzero(t5);
            uint256_t const m2 = s2;
            top[-2] = t2;
            top[-1] = m2;
            top[0] = t4;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1dbe); }
            MONAD_AOT_TAIL return b_1d69<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d69(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x91, 0x81, 0x88, 0x88, 0x88, 0x60, 0x96, 0x85, 0x96, 0x61, 0x57}, 9, 6));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x91, 0x81, 0x88, 0x88, 0x88, 0x60, 0x96, 0x85, 0x96, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            bool const j11 = aot::nonzero(s2);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const m2 = s2;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-3] = uint256_t{0x1ull};
            top[-2] = m3;
            top[-1] = m3;
            top[0] = m2;
            top[1] = m8;
            top[2] = m7;
            top[3] = m6;
            top[4] = m1;
            top += 4;
            if (j11) { MONAD_AOT_TAIL return b_1d84<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1d78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d78(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x01, 0x61, 0x56}, 8, 0));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = s6 + s7;
            top[-7] = t1;
            top += -7;
            MONAD_AOT_TAIL return b_1d31<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d84(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x95, 0x61, 0x92, 0x73, 0x61, 0x93, 0x51, 0x16, 0x95, 0x61, 0x56}, 6, 4));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x95, 0x61, 0x92, 0x73, 0x61, 0x93, 0x51, 0x16, 0x95, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-5] = uint256_t{0x1db3ull};
            top[-3] = t2;
            top[-1] = uint256_t{0x1dadull};
            top[0] = uint256_t{0x515ull};
            top[1] = m5;
            top[2] = m1;
            top[3] = m3;
            top += 3;
            MONAD_AOT_TAIL return b_196c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1dad(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x61, 0x56}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[0] = m2;
            MONAD_AOT_TAIL return b_18b5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1db3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x38, 0x88, 0x88, 0x88, 0x83, 0x61, 0x56}, 7, 7));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x38, 0x88, 0x88, 0x88, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[1] = m0;
            top[2] = uint256_t{0x23c0ull};
            top[3] = m6;
            top[4] = m5;
            top[5] = m4;
            top[6] = uint256_t{0x23c0ull};
            top += 6;
            MONAD_AOT_TAIL return b_1d78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1e47(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x73, 0x60, 0x60, 0x83, 0x16, 0x1b, 0x92, 0x16, 0x60, 0x52, 0x60, 0x60, 0x52, 0x60, 0x60, 0x20, 0x90, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x52, 0x60, 0x60, 0x20, 0x81, 0x81, 0x54, 0x18, 0x80, 0x91, 0x55, 0x16, 0x15, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x73, 0x60, 0x60, 0x83, 0x16, 0x1b, 0x92, 0x16, 0x60, 0x52, 0x60, 0x60, 0x52, 0x60, 0x60, 0x20, 0x90, 0x60, 0x1c, 0x60, 0x52, 0x60, 0x52, 0x60, 0x60, 0x20, 0x81, 0x81, 0x54, 0x18, 0x80, 0x91, 0x55, 0x16, 0x15, 0x61, 0x57}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 & uint256_t{0xffull};
            uint256_t const t2 = aot::shl(t1, uint256_t{0x1ull});
            uint256_t const &s0 = top[0];
            uint256_t const t3 = s0 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t4 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t5 = aot::shr_c<8>(s1);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t5);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t4);
            uint256_t const t6 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t7 = aot::sload<traits>(ctx, gas, t6);
            uint256_t const t8 = t7 ^ t2;
            aot::sstore<traits>(ctx, gas, t6, t8, (aot::gas_of<traits>({0x16, 0x15, 0x61, 0x57}) + 0));
            uint256_t const t9 = t8 & t2;
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            bool const j38 = aot::nonzero(t10);
            top += -2;
            if (j38) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1e91); }
            MONAD_AOT_TAIL return b_1e90<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e90(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ebb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            top[1] = uint256_t{0x1ec5ull};
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_15ef<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ec5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            top[1] = uint256_t{0x1ed2ull};
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_1437<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ed2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x81, 0x52, 0x7f, 0x61, 0x82, 0x94, 0x61, 0x56}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x81, 0x52, 0x7f, 0x61, 0x82, 0x94, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s0, s2);
            uint256_t const m0 = s0;
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[1] = uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            top[2] = uint256_t{0x1f00ull};
            top[3] = m2;
            top += 3;
            MONAD_AOT_TAIL return b_15ef<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f00(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f0a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x81, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(s0 == uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1f37); }
            MONAD_AOT_TAIL return b_1f32<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f32(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x01, 0x90, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x1ull} + s0;
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top[-1] = t1;
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f66(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x51, 0x60, 0x80, 0x92, 0x01, 0x91, 0x60}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x51, 0x60, 0x80, 0x92, 0x01, 0x91, 0x60}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = s0 + uint256_t{0x20ull};
            top[0] = t2;
            top[1] = t1;
            top[2] = uint256_t{0x20ull};
            top[3] = uint256_t{0x0ull};
            top += 3;
            MONAD_AOT_TAIL return b_1f71<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f71(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j5) { MONAD_AOT_TAIL return b_1f7f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1f79<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f79(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x90, 0x56}, 6, 0));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint64_t const jt = aot::jump_offset(s5);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-5] = m4;
            top += -5;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f7f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x51, 0x85, 0x52, 0x93, 0x81, 0x01, 0x93, 0x92, 0x81, 0x01, 0x92, 0x60, 0x01, 0x61, 0x56}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x51, 0x85, 0x52, 0x93, 0x81, 0x01, 0x93, 0x92, 0x81, 0x01, 0x92, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, s4, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s1 + s4;
            uint256_t const t3 = s1 + s3;
            uint256_t const &s0 = top[0];
            uint256_t const t4 = uint256_t{0x1ull} + s0;
            top[-4] = t2;
            top[-3] = t3;
            top[0] = t4;
            MONAD_AOT_TAIL return b_1f71<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f93(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x81, 0x51, 0x91, 0x60}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x81, 0x51, 0x91, 0x60}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const m0 = s0;
            top[-1] = t1;
            top[0] = m1;
            top[1] = m0;
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_1f9a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f9a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x81, 0x10, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x81, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::from_bool(s0 < s3);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1fab<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1fa2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fa2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x01, 0x60, 0x81, 0x52, 0x90, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x01, 0x60, 0x81, 0x52, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s2 + s3;
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull});
            uint256_t const &s4 = top[-4];
            uint64_t const jt = aot::jump_offset(s4);
            top[-4] = t1;
            top += -4;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1fab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x60, 0x80, 0x92, 0x84, 0x01, 0x01, 0x51, 0x81, 0x85, 0x01, 0x52, 0x01, 0x61, 0x56}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x60, 0x80, 0x92, 0x84, 0x01, 0x01, 0x51, 0x81, 0x85, 0x01, 0x52, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 + s0;
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = s2 + s0;
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const t5 = s0 + uint256_t{0x20ull};
            top[0] = t5;
            MONAD_AOT_TAIL return b_1f9a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1fbe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x81, 0x01, 0x91, 0x7f, 0x83, 0x52, 0x73, 0x80, 0x82, 0x51, 0x16, 0x60, 0x84, 0x01, 0x52, 0x60, 0x82, 0x01, 0x51, 0x16, 0x60, 0x83, 0x01, 0x52, 0x60, 0x65, 0x91, 0x82, 0x60, 0x82, 0x01, 0x51, 0x16, 0x60, 0x85, 0x01, 0x52, 0x01, 0x51, 0x16, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x60, 0x81, 0x01, 0x81, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}, 1, 7));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x81, 0x01, 0x91, 0x7f, 0x83, 0x52, 0x73, 0x80, 0x82, 0x51, 0x16, 0x60, 0x84, 0x01, 0x52, 0x60, 0x82, 0x01, 0x51, 0x16, 0x60, 0x83, 0x01, 0x52, 0x60, 0x65, 0x91, 0x82, 0x60, 0x82, 0x01, 0x51, 0x16, 0x60, 0x85, 0x01, 0x52, 0x01, 0x51, 0x16, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x60, 0x81, 0x01, 0x81, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x101849d5573b3678ull, 0x66f023ab9e8a83a7ull, 0xbf6f5ebea28756c9ull, 0x65626cad6cb96493ull});
            uint256_t const &s0 = top[0];
            uint256_t const t3 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t5 = t1 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const t6 = s0 + uint256_t{0x20ull};
            uint256_t const t7 = aot::mload<traits>(ctx, gas, t6);
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t9 = t1 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t9, t8);
            uint256_t const t10 = s0 + uint256_t{0x40ull};
            uint256_t const t11 = aot::mload<traits>(ctx, gas, t10);
            uint256_t const t12 = t11 & uint256_t{0xffffffffffffull};
            uint256_t const t13 = t1 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t13, t12);
            uint256_t const t14 = s0 + uint256_t{0x60ull};
            uint256_t const t15 = aot::mload<traits>(ctx, gas, t14);
            uint256_t const t16 = t15 & uint256_t{0xffffffffffffull};
            uint256_t const t17 = t1 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t17, t16);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0xa0ull});
            uint256_t const t18 = t1 + uint256_t{0xc0ull};
            uint256_t const t19 = aot::from_bool(t18 < t1);
            uint256_t const t20 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t18);
            uint256_t const t21 = t20 | t19;
            bool const j62 = aot::nonzero(t21);
            top[0] = t2;
            top[1] = t1;
            top[2] = t18;
            top += 2;
            if (j62) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x13b4); }
            MONAD_AOT_TAIL return b_204c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_204c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x52, 0x51, 0x90, 0x20, 0x90, 0x56}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x52, 0x51, 0x90, 0x20, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const &s2 = top[-2];
            auto const h4 = aot::sha3_any<traits>(ctx, gas, s2, t1);
            gas = ctx->gas_remaining;
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top[-3] = h4;
            top += -3;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2054(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x80, 0x82, 0x01, 0x92, 0x7f, 0x84, 0x52, 0x73, 0x81, 0x51, 0x16, 0x60, 0x84, 0x01, 0x52, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x61, 0x81, 0x61, 0x56}, 1, 6));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x80, 0x82, 0x01, 0x92, 0x7f, 0x84, 0x52, 0x73, 0x81, 0x51, 0x16, 0x60, 0x84, 0x01, 0x52, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0xde1adec9846d06a1ull, 0xbd48cd73c4a740aeull, 0x4f0cd8829da7e234ull, 0x618358ac3db8dc27ull});
            uint256_t const &s0 = top[0];
            uint256_t const t3 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t5 = t1 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const t6 = s0 + uint256_t{0x20ull};
            uint256_t const t7 = aot::mload<traits>(ctx, gas, t6);
            uint256_t const t8 = t1 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t8, t7);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x60ull});
            top[0] = t2;
            top[1] = t1;
            top[2] = uint256_t{0x1bd3ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_1398<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_20b1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x90, 0x82, 0x60, 0x91, 0x03, 0x12, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x90, 0x82, 0x60, 0x91, 0x03, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 - s0;
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x40ull}));
            bool const j9 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[-1] = m2;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x149b); }
            MONAD_AOT_TAIL return b_20be<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_20be(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x82, 0x35, 0x92, 0x01, 0x35, 0x90, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x82, 0x35, 0x92, 0x01, 0x35, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::calldataload(ctx, s1);
            uint256_t const t2 = s1 + uint256_t{0x20ull};
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top[-1] = t1;
            top[0] = t3;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_20c7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x84, 0x3b, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x84, 0x3b, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            ctx->gas_remaining = gas;
            uint256_t r3;
            runtime::extcodesize<traits>(ctx, &r3, &s3);
            gas = ctx->gas_remaining;
            bool const j5 = aot::nonzero(r3);
            top[1] = uint256_t{0x0ull};
            top += 1;
            if (j5) { MONAD_AOT_TAIL return b_222e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_20d0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_20d0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x60, 0x82, 0x03, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x60, 0x82, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 - uint256_t{0x41ull};
            bool const j5 = aot::nonzero(t1);
            top += -1;
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x21ac); }
            MONAD_AOT_TAIL return b_20d9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_20d9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x82, 0x82, 0x01, 0x82, 0x61, 0x56}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x82, 0x82, 0x01, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x20e4ull};
            top[2] = t1;
            top[3] = m0;
            top += 3;
            MONAD_AOT_TAIL return b_20b1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_20e4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x93, 0x90, 0x92, 0x60, 0x10, 0x15, 0x61, 0x57}, 5, 1));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x93, 0x90, 0x92, 0x60, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::from_bool(uint256_t{0x40ull} < s3);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j8 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-4] = m0;
            top[-3] = m1;
            top[-1] = m4;
            top += -1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1772); }
            MONAD_AOT_TAIL return b_20f0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_20f0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x93, 0x60, 0x93, 0x60, 0x60, 0x60, 0x95, 0x01, 0x35, 0x60, 0x1c}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x93, 0x60, 0x93, 0x60, 0x60, 0x60, 0x95, 0x01, 0x35, 0x60, 0x1c}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x40ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const t3 = aot::shr_c<248>(t2);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-3] = uint256_t{0x20ull};
            top[-2] = uint256_t{0x0ull};
            top[-1] = uint256_t{0x80ull};
            top[1] = m3;
            top[2] = m2;
            top[3] = uint256_t{0xffull};
            top[4] = t3;
            top += 4;
            MONAD_AOT_TAIL return b_2102<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2102(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x94, 0x85, 0x52, 0x16, 0x86, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x82, 0x80, 0x52, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x94, 0x85, 0x52, 0x16, 0x86, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x82, 0x80, 0x52, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, t1, s4);
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s0 & s1;
            uint256_t const &s7 = top[-7];
            uint256_t const t3 = t1 + s7;
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = t1 + uint256_t{0x40ull};
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t4, s2);
            uint256_t const t5 = t1 + uint256_t{0x60ull};
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, t5, s3);
            uint256_t const &s6 = top[-6];
            aot::mstore<traits>(ctx, gas, s6, s6);
            uint256_t const t6 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k24_1 = uint256_t{0x1ull};
            uint256_t const &s5 = top[-5];
            ctx->gas_remaining = gas;
            uint256_t r24;
            runtime::staticcall<traits>(ctx, &r24, &t6, &k24_1, &t1, &s5, &s6, &s7, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t7 = aot::from_bool(!aot::nonzero(r24));
            bool const j27 = aot::nonzero(t7);
            top += -8;
            if (j27) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x21a0); }
            MONAD_AOT_TAIL return b_2124<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2124(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x73, 0x80, 0x60, 0x51, 0x16, 0x91, 0x82, 0x15, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x73, 0x80, 0x60, 0x51, 0x16, 0x91, 0x82, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j9 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t2;
            top[1] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[2] = m0;
            top += 2;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2176); }
            MONAD_AOT_TAIL return b_2145<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2145(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x16, 0x03, 0x61, 0x57}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x16, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 & s1;
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = t1 - s2;
            bool const j3 = aot::nonzero(t2);
            top += -3;
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x214c); }
            MONAD_AOT_TAIL return b_214b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_214b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21b5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x91, 0x81, 0x01, 0x90, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x91, 0x81, 0x01, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x21c0ull};
            top[0] = t1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_20b1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21f5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x93, 0x60, 0x93, 0x60, 0x60, 0x94, 0x61, 0x56}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x93, 0x60, 0x93, 0x60, 0x60, 0x94, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-3] = uint256_t{0x20ull};
            top[-2] = uint256_t{0x0ull};
            top[-1] = uint256_t{0x80ull};
            top[1] = m3;
            top[2] = m2;
            top[3] = uint256_t{0xffull};
            top[4] = m1;
            top += 4;
            MONAD_AOT_TAIL return b_2102<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_222e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x93, 0x91, 0x60, 0x92, 0x81, 0x73, 0x60, 0x60, 0x95, 0x7f, 0x60, 0x51, 0x98, 0x89, 0x97, 0x88, 0x96, 0x87, 0x94, 0x7f, 0x9e, 0x8f, 0x87, 0x52, 0x60, 0x87, 0x01, 0x52, 0x60, 0x60, 0x87, 0x01, 0x52, 0x81, 0x60, 0x87, 0x01, 0x52, 0x86, 0x86, 0x01, 0x37, 0x8b, 0x85, 0x82, 0x86, 0x01, 0x01, 0x52, 0x01, 0x16, 0x81, 0x01, 0x03, 0x01, 0x92, 0x16, 0x5a, 0xfa, 0x90, 0x81, 0x15, 0x61, 0x57}, 5, 13));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1011)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x93, 0x91, 0x60, 0x92, 0x81, 0x73, 0x60, 0x60, 0x95, 0x7f, 0x60, 0x51, 0x98, 0x89, 0x97, 0x88, 0x96, 0x87, 0x94, 0x7f, 0x9e, 0x8f, 0x87, 0x52, 0x60, 0x87, 0x01, 0x52, 0x60, 0x60, 0x87, 0x01, 0x52, 0x81, 0x60, 0x87, 0x01, 0x52, 0x86, 0x86, 0x01, 0x37, 0x8b, 0x85, 0x82, 0x86, 0x01, 0x01, 0x52, 0x01, 0x16, 0x81, 0x01, 0x03, 0x01, 0x92, 0x16, 0x5a, 0xfa, 0x90, 0x81, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x1626ba7e00000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, t2, s3);
            uint256_t const t3 = t1 + uint256_t{0x24ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0x40ull});
            uint256_t const t4 = t1 + uint256_t{0x44ull};
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t4, s2);
            uint256_t const t5 = t1 + uint256_t{0x64ull};
            uint256_t const &s1 = top[-1];
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t5, &s1, &s2);
            gas = ctx->gas_remaining;
            uint256_t const t6 = t1 + s2;
            uint256_t const t7 = t6 + uint256_t{0x64ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t7, s0);
            uint256_t const t8 = s2 + uint256_t{0x1full};
            uint256_t const t9 = t8 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t10 = t1 + t9;
            uint256_t const t11 = t10 - t1;
            uint256_t const t12 = t11 + uint256_t{0x64ull};
            uint256_t const &s4 = top[-4];
            uint256_t const t13 = s4 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t14 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x90, 0x81, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k60_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r60;
            runtime::staticcall<traits>(ctx, &r60, &t14, &t13, &t1, &t12, &t1, &k60_5, (aot::gas_of<traits>({0x90, 0x81, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t15 = aot::from_bool(!aot::nonzero(r60));
            bool const j65 = aot::nonzero(t15);
            uint256_t const m0 = s0;
            top[-4] = uint256_t{0x0ull, 0x0ull, 0x0ull, 0x1626ba7e00000000ull};
            top[-3] = m0;
            top[-2] = r60;
            top[-1] = t1;
            top += -1;
            if (j65) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x23a8); }
            MONAD_AOT_TAIL return b_22ce<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_22ce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x91, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x91, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            bool const j3 = aot::nonzero(s1);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-1] = m2;
            if (j3) { MONAD_AOT_TAIL return b_232a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_22d4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_22d4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x7f, 0x91, 0x50, 0x16, 0x03, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x7f, 0x91, 0x50, 0x16, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 & uint256_t{0x0ull, 0x0ull, 0x0ull, 0xffffffff00000000ull};
            uint256_t const &s3 = top[-3];
            uint256_t const t2 = t1 - s3;
            bool const j8 = aot::nonzero(t2);
            top += -4;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2300); }
            MONAD_AOT_TAIL return b_22ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_22ff(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 9152)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_232a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x60, 0x81, 0x3d, 0x82, 0x11, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x60, 0x81, 0x3d, 0x82, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x20ull});
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top[0] = uint256_t{0x20ull};
            top[1] = m0;
            top += 1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x23a0); }
            MONAD_AOT_TAIL return b_2337<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2337(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x61, 0x60, 0x93, 0x83, 0x61, 0x56}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x61, 0x60, 0x93, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x20ull};
            top[1] = m1;
            top[2] = uint256_t{0x2344ull};
            top[3] = m1;
            top[4] = m0;
            top += 4;
            MONAD_AOT_TAIL return b_1437<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2344(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x01, 0x03, 0x12, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x01, 0x03, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 + s0;
            uint256_t const t2 = t1 - s1;
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = aot::from_bool(slt(t2, s2));
            bool const j6 = aot::nonzero(t3);
            top += -3;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x336); }
            MONAD_AOT_TAIL return b_234d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_234d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x51, 0x90, 0x7f, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x51, 0x90, 0x7f, 0x82, 0x16, 0x82, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = t1 & uint256_t{0x0ull, 0x0ull, 0x0ull, 0xffffffff00000000ull};
            uint256_t const t3 = t1 - t2;
            bool const j8 = aot::nonzero(t3);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[0] = m1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xa9a); }
            MONAD_AOT_TAIL return b_2378<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2378(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x7f, 0x90, 0x38, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x7f, 0x90, 0x38, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = uint256_t{0x0ull, 0x0ull, 0x0ull, 0xffffffff00000000ull};
            top[0] = m1;
            top[1] = uint256_t{0x23c0ull};
            top += 1;
            MONAD_AOT_TAIL return b_22d4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        void run(
            void *, Context *const ctx, interpreter::Intercode const *,
            uint256_t *const stack_ptr, void *)
        {
            b_0<traits>(ctx, stack_ptr - 1, stack_ptr - 1, ctx->gas_remaining);
        }
    }

    template void c_c67d1657868aa514::run<EvmTraits<MONAD_ETH_OSAKA>>(
        void *, Context *, interpreter::Intercode const *, uint256_t *, void *);
}
