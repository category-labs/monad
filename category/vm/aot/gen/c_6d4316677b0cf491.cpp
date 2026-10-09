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

// Written by aotgen.py from the code whose keccak is 6d4316677b0cf491853e301d8ad6147f49e81f86dfb42283d98ca076ec92c826: not to be edited.

#include <category/vm/aot/ops.hpp>
#include <category/vm/interpreter/execute.hpp>
#include <category/vm/interpreter/intercode.hpp>

#define MONAD_AOT_TAIL __attribute__((musttail))

namespace monad::vm::aot
{
    using runtime::Context;
    using runtime::StatusCode;

    // 14435 bytes, keccak 6d4316677b0cf491853e301d8ad6147f49e81f86dfb42283d98ca076ec92c826
    namespace c_6d4316677b0cf491
    {
        template <Traits traits>
        using Block = void (*)(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_6b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_7b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_b5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ca(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ee(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_146(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1df(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_227(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_263(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_325(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_330(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_333(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_339(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_36e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_397(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3ab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3b1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3d5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3db(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3ef(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3f5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_42a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_434(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_44d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_453(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_45d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_476(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_47c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_4b1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4e6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_4ea(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4f0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_525(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_56b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_575(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_57a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_583(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_58b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_590(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_592(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_59c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_5ac(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_5ed(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_5f3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_618(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_65b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_666(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_66d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6ab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_6e6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_6e8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_726(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_72e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_73a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_740(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_775(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_778(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_77f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_788(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_7c6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_7c9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_82a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_831(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_855(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_89a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_8ae(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_8b1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_8bc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_8c3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_92a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_931(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_955(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_95f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_96a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_976(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_97c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_9b1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_9bb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9f1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_9fd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a03(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_a38(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_a46(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_aea(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b02(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b0e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b16(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b25(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b37(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b3f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b4b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b56(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b64(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b69(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b71(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b77(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b8a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_bc6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c14(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_c44(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_cbf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ccb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d00(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d03(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d0a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d22(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d2e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d36(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d45(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d57(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d5f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d6b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d76(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d84(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d89(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d91(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_d97(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_dab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_deb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e39(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e69(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_edd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ee9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_f1e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_f21(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f69(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_f73(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f8f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_f93(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f99(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_fde(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_fed(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1001(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_100b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1021(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1051(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1056(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1070(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_107a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1096(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_109a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10a0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_10d5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_10e5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10f4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1108(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1112(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1128(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1158(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_115d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1165(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1171(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_117b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1186(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_119a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_11cb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11d6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_120b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1228(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1230(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1234(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_123c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1264(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_126b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_126f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1275(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_127d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_128a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12a7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12ba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_12cd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12d3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_12db(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_12ea(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12f2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_130f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1322(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1335(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_133b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1343(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1352(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_135b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_13a0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_13b6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_13f6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_14d7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_151e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1528(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_152c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1533(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1558(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_155e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1567(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_15a4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_15c3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_15d1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1604(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1612(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_161a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_161f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1621(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_162c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1635(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1639(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1643(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1647(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_164e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_167e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1684(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_16c1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_16ce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_16d3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_16dd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_16e9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_16f4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1732(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1738(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1748(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1751(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1758(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_176c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1773(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_177c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1787(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_17a8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_17ad(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_17af(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1841(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1867(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18ed(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18fe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1907(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1910(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_191a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_195d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1992(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_19b1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a21(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a40(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1a7c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1a85(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b0d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b20(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b36(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b51(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b5a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b66(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ba9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1bde(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1bfe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c41(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c76(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c96(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1cd2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1cdc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ced(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1cfb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1d05(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1d0f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1d12(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d18(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d74(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d82(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dad(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1deb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1def(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1df5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1dfb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e39(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1eb3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ee5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f65(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f73(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1f7f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1f83(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fc1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_203b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_206d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_20ec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_20ef(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_210e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2111(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2117(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_214d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2174(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2177(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_217d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2182(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2188(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_218f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21b3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_21ba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21c6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_21e1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_220f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_223c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2248(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2264(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2273(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2290(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2297(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_22a9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_22fd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2320(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2325(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2327(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2367(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_239c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_23bb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_23c4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_23ca(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_23ff(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_241b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_241e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_245d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2482(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_248b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24aa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24b5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_24c3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_24cb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24da(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24e4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24f0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24f7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2503(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_250f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2518(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2523(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2539(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2558(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2562(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_256a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_259f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_25a6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_25b3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_25ba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_25d5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_25ec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_25f8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2602(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2611(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2619(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2620(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_263d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_267f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_26a7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_26af(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_26c8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_26d2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_26f7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2708(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_270c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_271a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2732(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2767(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2775(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2844(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_284a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2852(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2858(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_286f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2873(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2879(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_28ae(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_28b3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_28cf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_28d5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_28e6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_28ed(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_28fa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2901(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_290c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2913(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_291d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2924(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_292e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2935(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_293f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2946(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2950(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2956(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_295d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2963(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_296d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_296f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2982(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2992(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_29bd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_29c8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_29cb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_29d9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_29fc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2a01(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2a03(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2a43(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2a78(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2a97(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2aa0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2aa6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2adb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2af7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2afa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b1c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b2a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b32(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b41(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b4d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b54(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b64(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b6e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b79(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b8f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2bae(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2bb8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2bbc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2bc2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2bf7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2c02(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2c13(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2c2b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2c60(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2c6e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2cf7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d10(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d5b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2d8f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2da2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2dd8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e16(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e76(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ea8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2f12(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2f50(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2fb0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2fe2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_304c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_30b6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_30ec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_30f2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3112(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_315f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3177(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3183(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_31b3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_31b6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_31c5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_31e1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3204(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_320f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3216(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3262(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_326c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3276(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3281(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3284(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_32a1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_32c8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_32d2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_32fe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3320(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_332c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3348(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_339c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_33c1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3423(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3455(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_34aa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_34b1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_34d1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_34d4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_34d9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_34e6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_34e9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_34fd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3500(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3514(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3517(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_351e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3531(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3534(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_353d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3559(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3567(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_357f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3582(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_358e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_35b3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_35f3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3641(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_366a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3671(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3677(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3683(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_36b7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_36c4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_36c7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_36ce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_373e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_374a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3751(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3761(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3768(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_376f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3776(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_377b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_37ab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_37b2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_37bf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_37c6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_37cd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_37d4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3821(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3828(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        void bad(Context *const ctx, uint256_t const *, uint256_t *, int64_t)
        {
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        inline constexpr Block<traits> jump_table[14435] = {
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3f<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_6b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &b_b5<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_ca<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_325<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_333<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_36e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3ab<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3d5<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3ef<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_42a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_44d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_476<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_4b1<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_4ea<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_525<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_56b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_57a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_583<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_590<traits>, &bad<traits>, &b_592<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_59c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_5ed<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_618<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_65b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_6e6<traits>, &bad<traits>, &b_6e8<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_73a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_775<traits>, &bad<traits>, &bad<traits>, &b_778<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_7c6<traits>, &bad<traits>,
            &bad<traits>, &b_7c9<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_831<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_855<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_89a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_8b1<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_8c3<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_931<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_955<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_95f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_976<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_9b1<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_9bb<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_9fd<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_a38<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_a46<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_b02<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_b25<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_b37<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_b3f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_b4b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_b56<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_b69<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_b71<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_b77<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_b8a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_cbf<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_d00<traits>, &bad<traits>,
            &bad<traits>, &b_d03<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_d22<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_d45<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_d57<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_d5f<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_d6b<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_d76<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_d89<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_d91<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_d97<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_dab<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &b_edd<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_f1e<traits>, &bad<traits>, &bad<traits>, &b_f21<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_f69<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_f73<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_f93<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_fce<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_fde<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1001<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_100b<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1056<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1070<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_107a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_109a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_10d5<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_10e5<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1108<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1112<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_115d<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1171<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_117b<traits>,
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
            &bad<traits>, &b_11cb<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_120b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1230<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1234<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_126b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_126f<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &b_127d<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &b_12cd<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &b_12db<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_12ea<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1335<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &b_1343<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1352<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &b_151e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_152c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1558<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_15d1<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1612<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_161f<traits>,
            &bad<traits>, &b_1621<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1635<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1639<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1647<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_167e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_16ce<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_16d3<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_16dd<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_16e9<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_16f4<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1751<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_176c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_177c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1787<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_17ad<traits>, &bad<traits>, &b_17af<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1841<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1867<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1a7c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1a85<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1cd2<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1cdc<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1cfb<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1d05<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1d0f<traits>,
            &bad<traits>, &bad<traits>, &b_1d12<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1deb<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1def<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1df5<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1dfb<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1f7f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1f83<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &b_20ef<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2111<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_214d<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2177<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2182<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_218f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_21ba<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &b_220f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_223c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2273<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2297<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_22a9<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_22fd<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2325<traits>, &bad<traits>, &b_2327<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_239c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_23c4<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_23ff<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_241e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &b_24aa<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_24b5<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_24da<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_24e4<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_24f0<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_24f7<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_2503<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_250f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2518<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2523<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &b_2558<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_259f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_25ec<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_25f8<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &b_26c8<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_270c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_271a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_2767<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2775<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2844<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2852<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2858<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2873<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_28ae<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_28b3<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_28d5<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_28ed<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2901<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2913<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2924<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_2935<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2946<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2956<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2963<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_296f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_29bd<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_29cb<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_29d9<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_2a01<traits>, &bad<traits>, &b_2a03<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2a78<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2aa0<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2adb<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2afa<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2b1c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2b41<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2b4d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2b54<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2b64<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2b6e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2b79<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &b_2bae<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2bbc<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2bf7<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2c02<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2c13<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2c60<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2c6e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2d8f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2dd8<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &b_2f12<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_304c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_30ec<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_30f2<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3183<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_31b6<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_31c5<traits>, &bad<traits>, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_320f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3216<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3262<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_326c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3276<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_3284<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &b_32d2<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_34b1<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_34d4<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_34d9<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_34e9<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_3500<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_3517<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_351e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3534<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_353d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_3559<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3567<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3582<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_358e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3641<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3671<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3677<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &b_36b7<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_36c7<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_36ce<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_373e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_3751<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3768<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_3776<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_377b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_37b2<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_37c6<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_37d4<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3828<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
        };

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x52, 0x60, 0x36, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x52, 0x60, 0x36, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, uint256_t{0x80ull});
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x4ull});
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x28); }
            MONAD_AOT_TAIL return b_d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x35, 0x60, 0x1c, 0x80, 0x63, 0x14, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x35, 0x60, 0x1c, 0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x0ull});
            uint256_t const t2 = aot::shr_c<224>(t1);
            uint256_t const t3 = aot::from_bool(uint256_t{0xad967e15ull} == t2);
            bool const j8 = aot::nonzero(t3);
            top[1] = t2;
            top += 1;
            if (j8) { MONAD_AOT_TAIL return b_2c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xdacb5419ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x58); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x28);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x36, 0x60, 0x61, 0x56}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x36, 0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            top[1] = uint256_t{0x3full};
            top[2] = uint256_t{0x3aull};
            top[3] = t1;
            top[4] = uint256_t{0x4ull};
            top += 4;
            MONAD_AOT_TAIL return b_351e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_6b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x80, 0x51, 0x92, 0x83, 0x52, 0x60, 0x83, 0x01, 0x91, 0x90, 0x91, 0x52, 0x01, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x80, 0x51, 0x92, 0x83, 0x52, 0x60, 0x83, 0x01, 0x91, 0x90, 0x91, 0x52, 0x01, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t1, s1);
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t2, s0);
            uint256_t const t3 = uint256_t{0x40ull} + t1;
            uint256_t const t4 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t5 = t3 - t4;
            aot::finish(ctx, gas, StatusCode::Success, t4, t5);
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_6b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x5f, 0x60, 0x60, 0x16, 0x60, 0x54, 0x03, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x5f, 0x60, 0x60, 0x16, 0x60, 0x54, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::sload<traits>(ctx, gas, uint256_t{0x1ull});
            uint256_t const t2 = t1 - uint256_t{0x2ull};
            bool const j10 = aot::nonzero(t2);
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top += 2;
            if (j10) { MONAD_AOT_TAIL return b_b5<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_7b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_7b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2ee1ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_b5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x55, 0x61, 0x5f, 0x8a, 0x8a, 0x8a, 0x8a, 0x8a, 0x8a, 0x8a, 0x61, 0x56}, 9, 10));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x55, 0x61, 0x5f, 0x8a, 0x8a, 0x8a, 0x8a, 0x8a, 0x8a, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::sstore<traits>(ctx, gas, uint256_t{0x1ull}, uint256_t{0x2ull}, (aot::gas_of<traits>({0x61, 0x5f, 0x8a, 0x8a, 0x8a, 0x8a, 0x8a, 0x8a, 0x8a, 0x61, 0x56}) + 0));
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
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
            top[1] = uint256_t{0xcaull};
            top[2] = uint256_t{0x0ull};
            top[3] = m8;
            top[4] = m7;
            top[5] = m6;
            top[6] = m5;
            top[7] = m4;
            top[8] = m3;
            top[9] = m2;
            top += 9;
            MONAD_AOT_TAIL return b_325<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ca(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x80, 0x55, 0x90, 0x9a, 0x90, 0x99, 0x50, 0x97, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}, 12, 2));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x80, 0x55, 0x90, 0x9a, 0x90, 0x99, 0x50, 0x97, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::sstore<traits>(ctx, gas, uint256_t{0x1ull}, uint256_t{0x1ull}, (aot::gas_of<traits>({0x90, 0x9a, 0x90, 0x99, 0x50, 0x97, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}) + 0));
            uint256_t const &s11 = top[-11];
            uint64_t const jt = aot::jump_offset(s11);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-11] = m1;
            top[-10] = m0;
            top += -10;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ee(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2ee1ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_146(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x33, 0x61, 0x7f, 0x54, 0x90, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x33, 0x61, 0x7f, 0x54, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t2 = aot::sload<traits>(ctx, gas, uint256_t{0xd6a717850b5d6103ull, 0x243e63b6e8ee1178ull, 0x73ae13b9f8a6016eull, 0xb53127684a568b31ull});
            top[0] = t1;
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x16f);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b0bull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1df(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b0dull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x5f, 0x85, 0x13}, 6, 1));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x5f, 0x85, 0x13}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s5));
            top[0] = t1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x221);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_227(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b0cull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_263(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b0eull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_325(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x80, 0x87, 0x15, 0x80, 0x15, 0x61, 0x57}, 6, 5));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x80, 0x87, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s5));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j8 = aot::nonzero(t2);
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top[3] = t1;
            top += 3;
            if (j8) { MONAD_AOT_TAIL return b_333<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_330<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_330(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x86, 0x15}, 8, 0));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x86, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s7));
            top[0] = t1;
            MONAD_AOT_TAIL return b_333<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_333(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_36e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_339<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_339(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2afdull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_36e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x88, 0x12, 0x80, 0x61, 0x57}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x88, 0x12, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::from_bool(slt(s7, uint256_t{0x0ull, 0x8000000000000000ull, 0xffffffffffffffffull, 0xffffffffffffffffull}));
            bool const j6 = aot::nonzero(t1);
            top[1] = t1;
            top += 1;
            if (j6) { MONAD_AOT_TAIL return b_3ab<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_397<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_397(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x6f, 0x88, 0x13}, 9, 1));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x6f, 0x88, 0x13}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0xffffffffffffffffull, 0x7fffffffffffffffull, 0x0ull, 0x0ull}, s8));
            top[0] = t1;
            MONAD_AOT_TAIL return b_3ab<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3ab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j3 = aot::nonzero(s0);
            if (j3) { MONAD_AOT_TAIL return b_3d5<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3b1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3b1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x7f, 0x87, 0x12}, 8, 1));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x7f, 0x87, 0x12}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::from_bool(slt(s7, uint256_t{0x0ull, 0x8000000000000000ull, 0xffffffffffffffffull, 0xffffffffffffffffull}));
            top[0] = t1;
            MONAD_AOT_TAIL return b_3d5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3d5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j3 = aot::nonzero(s0);
            if (j3) { MONAD_AOT_TAIL return b_3ef<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3db<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3db(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x6f, 0x87, 0x13}, 8, 1));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x6f, 0x87, 0x13}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0xffffffffffffffffull, 0x7fffffffffffffffull, 0x0ull, 0x0ull}, s7));
            top[0] = t1;
            MONAD_AOT_TAIL return b_3ef<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3ef(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_42a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3f5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3f5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2afeull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_42a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x88, 0x12, 0x80, 0x15, 0x61, 0x57}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x88, 0x12, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::from_bool(slt(s7, uint256_t{0x0ull}));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return b_44d<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_434<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_434(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x73, 0x86, 0x16, 0x15}, 7, 1));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x73, 0x86, 0x16, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s6 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            top[0] = t2;
            MONAD_AOT_TAIL return b_44d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_44d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j3 = aot::nonzero(s0);
            if (j3) { MONAD_AOT_TAIL return b_476<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_453<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_453(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x5f, 0x87, 0x13, 0x80, 0x15, 0x61, 0x57}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x5f, 0x87, 0x13, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s7));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_476<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_45d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_45d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x73, 0x85, 0x16, 0x15}, 6, 1));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x73, 0x85, 0x16, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = s5 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            top[0] = t2;
            MONAD_AOT_TAIL return b_476<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_476(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_4b1<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_47c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_47c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b00ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_4b1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x89, 0x16, 0x73, 0x14, 0x80, 0x15, 0x90, 0x61, 0x57}, 9, 3));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x89, 0x16, 0x73, 0x14, 0x80, 0x15, 0x90, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = s8 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = aot::from_bool(uint256_t{0xeeeeeeeeeeeeeeeeull, 0xeeeeeeeeeeeeeeeeull, 0xeeeeeeeeull, 0x0ull} == t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j10 = aot::nonzero(t2);
            top[1] = t3;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return b_4ea<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_4e6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4e6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x5f, 0x34, 0x11}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x5f, 0x34, 0x11}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = aot::from_bool(uint256_t{0x0ull} < t1);
            top[0] = t2;
            MONAD_AOT_TAIL return b_4ea<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_4ea(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_525<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_4f0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4f0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b02ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_525(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x51, 0x80, 0x61, 0x01, 0x60, 0x52, 0x80, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x50, 0x90, 0x56}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x51, 0x80, 0x61, 0x01, 0x60, 0x52, 0x80, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x81, 0x52, 0x50, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = uint256_t{0x120ull} + t1;
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t2);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull});
            uint256_t const t3 = uint256_t{0x20ull} + t1;
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0x0ull});
            uint256_t const t4 = uint256_t{0x20ull} + t3;
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x0ull});
            uint256_t const t5 = uint256_t{0x20ull} + t4;
            aot::mstore<traits>(ctx, gas, t5, uint256_t{0x0ull});
            uint256_t const t6 = uint256_t{0x20ull} + t5;
            aot::mstore<traits>(ctx, gas, t6, uint256_t{0x0ull});
            uint256_t const t7 = uint256_t{0x20ull} + t6;
            aot::mstore<traits>(ctx, gas, t7, uint256_t{0x0ull});
            uint256_t const t8 = uint256_t{0x20ull} + t7;
            aot::mstore<traits>(ctx, gas, t8, uint256_t{0x0ull});
            uint256_t const t9 = uint256_t{0x20ull} + t8;
            aot::mstore<traits>(ctx, gas, t9, uint256_t{0x0ull});
            uint256_t const t10 = uint256_t{0x20ull} + t9;
            aot::mstore<traits>(ctx, gas, t10, uint256_t{0x0ull});
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_56b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_56b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x5f, 0x5f, 0x8a, 0x12, 0x61, 0x57}, 8, 4));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x5f, 0x5f, 0x8a, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::from_bool(slt(s7, uint256_t{0x0ull}));
            bool const j7 = aot::nonzero(t1);
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top += 2;
            if (j7) { MONAD_AOT_TAIL return b_57a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_575<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_575(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_583<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_57a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x8a, 0x61, 0x56}, 10, 3));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[1] = uint256_t{0x583ull};
            top[2] = m9;
            top += 2;
            MONAD_AOT_TAIL return b_3641<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_583(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x8c, 0x13, 0x61, 0x57}, 12, 2));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x8c, 0x13, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s11));
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_590<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_58b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_58b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_592<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_590(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x8b}, 12, 1));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x8b}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            top[1] = m11;
            top += 1;
            MONAD_AOT_TAIL return b_592<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_592(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x59cull};
            top[0] = m1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_59c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x95, 0x50, 0x90, 0x50, 0x60, 0x86, 0x11, 0x15, 0x61, 0x57}, 7, 1));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x95, 0x50, 0x90, 0x50, 0x60, 0x86, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::from_bool(uint256_t{0x3full} < s6);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j11 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-5] = uint256_t{0x64ull};
            top[-1] = m0;
            top += -1;
            if (j11) { MONAD_AOT_TAIL return b_6e8<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_5ac<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_5ac(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x8b, 0x8b, 0x8b, 0x8b, 0x8b, 0x8b, 0x80, 0x80, 0x60, 0x01, 0x60, 0x80, 0x91, 0x04, 0x02, 0x60, 0x01, 0x60, 0x51, 0x90, 0x81, 0x01, 0x60, 0x52, 0x80, 0x93, 0x92, 0x91, 0x90, 0x81, 0x81, 0x52, 0x60, 0x01, 0x83, 0x83, 0x80, 0x82, 0x84, 0x37, 0x5f, 0x92, 0x01, 0x91, 0x90, 0x91, 0x52, 0x50, 0x61, 0x92, 0x50, 0x50, 0x50, 0x56}, 11, 15));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1009)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x8b, 0x8b, 0x8b, 0x8b, 0x8b, 0x8b, 0x80, 0x80, 0x60, 0x01, 0x60, 0x80, 0x91, 0x04, 0x02, 0x60, 0x01, 0x60, 0x51, 0x90, 0x81, 0x01, 0x60, 0x52, 0x80, 0x93, 0x92, 0x91, 0x90, 0x81, 0x81, 0x52, 0x60, 0x01, 0x83, 0x83, 0x80, 0x82, 0x84, 0x37, 0x5f, 0x92, 0x01, 0x91, 0x90, 0x91, 0x52, 0x50, 0x61, 0x92, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = uint256_t{0x1full} + s5;
            uint256_t const t2 = aot::shr_c<5>(t1);
            uint256_t const t3 = aot::shl_c<5>(t2);
            uint256_t const t4 = uint256_t{0x20ull} + t3;
            uint256_t const t5 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t6 = t5 + t4;
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t6);
            aot::mstore<traits>(ctx, gas, t5, s5);
            uint256_t const t7 = uint256_t{0x20ull} + t5;
            uint256_t const &s6 = top[-6];
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t7, &s6, &s5);
            gas = ctx->gas_remaining;
            uint256_t const t8 = t7 + s5;
            aot::mstore<traits>(ctx, gas, t8, uint256_t{0x0ull});
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[1] = uint256_t{0x5edull};
            top[2] = m10;
            top[3] = m9;
            top[4] = m8;
            top[5] = m7;
            top[6] = t5;
            top += 6;
            MONAD_AOT_TAIL return b_1867<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_5ed(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_618<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_5f3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_5f3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x7f, 0x82, 0x52, 0x5f}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x7f, 0x82, 0x52, 0x5f}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            top[0] = uint256_t{0x0ull};
            MONAD_AOT_TAIL return b_618<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_618(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x61, 0x8c, 0x8c, 0x8c, 0x8c, 0x8c, 0x8c, 0x80, 0x80, 0x60, 0x01, 0x60, 0x80, 0x91, 0x04, 0x02, 0x60, 0x01, 0x60, 0x51, 0x90, 0x81, 0x01, 0x60, 0x52, 0x80, 0x93, 0x92, 0x91, 0x90, 0x81, 0x81, 0x52, 0x60, 0x01, 0x83, 0x83, 0x80, 0x82, 0x84, 0x37, 0x5f, 0x92, 0x01, 0x91, 0x90, 0x91, 0x52, 0x50, 0x61, 0x92, 0x50, 0x50, 0x50, 0x56}, 11, 16));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1008)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x61, 0x8c, 0x8c, 0x8c, 0x8c, 0x8c, 0x8c, 0x80, 0x80, 0x60, 0x01, 0x60, 0x80, 0x91, 0x04, 0x02, 0x60, 0x01, 0x60, 0x51, 0x90, 0x81, 0x01, 0x60, 0x52, 0x80, 0x93, 0x92, 0x91, 0x90, 0x81, 0x81, 0x52, 0x60, 0x01, 0x83, 0x83, 0x80, 0x82, 0x84, 0x37, 0x5f, 0x92, 0x01, 0x91, 0x90, 0x91, 0x52, 0x50, 0x61, 0x92, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = uint256_t{0x1full} + s5;
            uint256_t const t2 = aot::shr_c<5>(t1);
            uint256_t const t3 = aot::shl_c<5>(t2);
            uint256_t const t4 = uint256_t{0x20ull} + t3;
            uint256_t const t5 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t6 = t5 + t4;
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t6);
            aot::mstore<traits>(ctx, gas, t5, s5);
            uint256_t const t7 = uint256_t{0x20ull} + t5;
            uint256_t const &s6 = top[-6];
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t7, &s6, &s5);
            gas = ctx->gas_remaining;
            uint256_t const t8 = t7 + s5;
            aot::mstore<traits>(ctx, gas, t8, uint256_t{0x0ull});
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x65bull};
            top[3] = m10;
            top[4] = m9;
            top[5] = m8;
            top[6] = m7;
            top[7] = t5;
            top += 7;
            MONAD_AOT_TAIL return b_1a85<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_65b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x93, 0x50, 0x90, 0x50, 0x80, 0x15, 0x61, 0x57}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x93, 0x50, 0x90, 0x50, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s1));
            bool const j8 = aot::nonzero(t1);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m1 = s1;
            top[-4] = m0;
            top[-2] = m1;
            top += -2;
            if (j8) { MONAD_AOT_TAIL return b_6e6<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_666<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_666(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x83, 0x03, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x83, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s2 - s1;
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x6a2); }
            MONAD_AOT_TAIL return b_66d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_66d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b0aull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6ab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x84, 0x52, 0x61, 0x90, 0x95, 0x02, 0x94, 0x90, 0x82, 0x90, 0x03, 0x90, 0x61, 0x56}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x84, 0x52, 0x61, 0x90, 0x95, 0x02, 0x94, 0x90, 0x82, 0x90, 0x03, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = aot::mul(s5, uint256_t{0x3e8ull});
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s1 - s2;
            top[-5] = t1;
            top[-1] = t2;
            MONAD_AOT_TAIL return b_6e6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_6e6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top += -1;
            MONAD_AOT_TAIL return b_6e8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_6e8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x73, 0x8d, 0x16, 0x01, 0x61, 0x57}, 12, 3));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x73, 0x8d, 0x16, 0x01, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = s11 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = t1 + uint256_t{0x1111111111111112ull, 0x1111111111111111ull, 0xffffffff11111111ull, 0xffffffffffffffffull};
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return b_778<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_726<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_726(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x34, 0x81, 0x11, 0x80, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x34, 0x81, 0x11, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::from_bool(t1 < s0);
            bool const j5 = aot::nonzero(t2);
            top[1] = t2;
            top += 1;
            if (j5) { MONAD_AOT_TAIL return b_73a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_72e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_72e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x61, 0x85, 0x81, 0x01, 0x82, 0x02, 0x04, 0x34, 0x11}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x61, 0x85, 0x81, 0x01, 0x82, 0x02, 0x04, 0x34, 0x11}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = uint256_t{0x2710ull} + s5;
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::mul(s1, t1);
            uint256_t const t3 = aot::udiv(t2, uint256_t{0x2710ull});
            uint256_t const t4 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t5 = aot::from_bool(t3 < t4);
            top[0] = t5;
            MONAD_AOT_TAIL return b_73a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_73a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_775<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_740<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_740(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b01ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_775(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x5f}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x5f}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[0] = uint256_t{0x0ull};
            MONAD_AOT_TAIL return b_778<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_778(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_9bb<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_77f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_77f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x86, 0x11, 0x15, 0x61, 0x57}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x86, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = aot::from_bool(uint256_t{0x5full} < s5);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j5 = aot::nonzero(t2);
            if (j5) { MONAD_AOT_TAIL return b_7c9<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_788<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_788(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x81, 0x88, 0x88, 0x80, 0x80, 0x60, 0x01, 0x60, 0x80, 0x91, 0x04, 0x02, 0x60, 0x01, 0x60, 0x51, 0x90, 0x81, 0x01, 0x60, 0x52, 0x80, 0x93, 0x92, 0x91, 0x90, 0x81, 0x81, 0x52, 0x60, 0x01, 0x83, 0x83, 0x80, 0x82, 0x84, 0x37, 0x5f, 0x92, 0x01, 0x91, 0x90, 0x91, 0x52, 0x50, 0x61, 0x92, 0x50, 0x50, 0x50, 0x56}, 7, 12));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1012)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x81, 0x88, 0x88, 0x80, 0x80, 0x60, 0x01, 0x60, 0x80, 0x91, 0x04, 0x02, 0x60, 0x01, 0x60, 0x51, 0x90, 0x81, 0x01, 0x60, 0x52, 0x80, 0x93, 0x92, 0x91, 0x90, 0x81, 0x81, 0x52, 0x60, 0x01, 0x83, 0x83, 0x80, 0x82, 0x84, 0x37, 0x5f, 0x92, 0x01, 0x91, 0x90, 0x91, 0x52, 0x50, 0x61, 0x92, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = uint256_t{0x1full} + s5;
            uint256_t const t2 = aot::shr_c<5>(t1);
            uint256_t const t3 = aot::shl_c<5>(t2);
            uint256_t const t4 = uint256_t{0x20ull} + t3;
            uint256_t const t5 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t6 = t5 + t4;
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t6);
            aot::mstore<traits>(ctx, gas, t5, s5);
            uint256_t const t7 = uint256_t{0x20ull} + t5;
            uint256_t const &s6 = top[-6];
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t7, &s6, &s5);
            gas = ctx->gas_remaining;
            uint256_t const t8 = t7 + s5;
            aot::mstore<traits>(ctx, gas, t8, uint256_t{0x0ull});
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x7c6ull};
            top[2] = m0;
            top[3] = t5;
            top += 3;
            MONAD_AOT_TAIL return b_1cdc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_7c6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            MONAD_AOT_TAIL return b_7c9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_7c9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x7f, 0x81, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x73, 0x8d, 0x16, 0x90, 0x63, 0x90, 0x60, 0x01, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x86, 0x5a, 0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}, 12, 9));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x7f, 0x81, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x73, 0x8d, 0x16, 0x90, 0x63, 0x90, 0x60, 0x01, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x86, 0x5a, 0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x70a0823100000000ull});
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t3 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const &s11 = top[-11];
            uint256_t const t4 = s11 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t5 = uint256_t{0x24ull} + t1;
            uint256_t const t6 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t7 = t5 - t6;
            uint256_t const t8 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k28_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r28;
            runtime::staticcall<traits>(ctx, &r28, &t8, &t4, &t6, &t7, &t6, &k28_5, (aot::gas_of<traits>({0x15, 0x80, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(r28));
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            bool const j33 = aot::nonzero(t10);
            top[1] = t4;
            top[2] = uint256_t{0x70a08231ull};
            top[3] = t5;
            top[4] = t9;
            top += 4;
            if (j33) { MONAD_AOT_TAIL return b_831<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_82a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_82a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const k3_0 = uint256_t{0x0ull};
            uint256_t const k3_1 = uint256_t{0x0ull};
            ctx->gas_remaining = gas;
            runtime::returndatacopy<traits>(ctx, &k3_0, &k3_1, &t1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, t2);
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_831(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x60, 0x51, 0x3d, 0x60, 0x19, 0x60, 0x82, 0x01, 0x16, 0x82, 0x01, 0x80, 0x60, 0x52, 0x50, 0x81, 0x01, 0x90, 0x61, 0x91, 0x90, 0x61, 0x56}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x60, 0x51, 0x3d, 0x60, 0x19, 0x60, 0x82, 0x01, 0x16, 0x82, 0x01, 0x80, 0x60, 0x52, 0x50, 0x81, 0x01, 0x90, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t3 = t2 + uint256_t{0x1full};
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t5 = t1 + t4;
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t5);
            uint256_t const t6 = t1 + t2;
            top[-3] = uint256_t{0x855ull};
            top[-2] = t6;
            top[-1] = t1;
            top += -1;
            MONAD_AOT_TAIL return b_36b7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_855(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x7f, 0x81, 0x52, 0x90, 0x92, 0x50, 0x33, 0x90, 0x63, 0x90, 0x61, 0x90, 0x8f, 0x90, 0x85, 0x90, 0x8c, 0x90, 0x8c, 0x90, 0x60, 0x01, 0x61, 0x56}, 13, 8));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x7f, 0x81, 0x52, 0x90, 0x92, 0x50, 0x33, 0x90, 0x63, 0x90, 0x61, 0x90, 0x8f, 0x90, 0x85, 0x90, 0x8c, 0x90, 0x8c, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xad20750100000000ull});
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t3 = uint256_t{0x4ull} + t1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-2] = m0;
            top[0] = t2;
            top[1] = uint256_t{0xad207501ull};
            top[2] = uint256_t{0x89aull};
            top[3] = m12;
            top[4] = m1;
            top[5] = m7;
            top[6] = m6;
            top[7] = t3;
            top += 7;
            MONAD_AOT_TAIL return b_36ce<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_89a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x5f, 0x87, 0x80, 0x3b, 0x15, 0x80, 0x15, 0x61, 0x57}, 3, 9));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x5f, 0x87, 0x80, 0x3b, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 - t1;
            uint256_t const &s2 = top[-2];
            ctx->gas_remaining = gas;
            uint256_t r11;
            runtime::extcodesize<traits>(ctx, &r11, &s2);
            gas = ctx->gas_remaining;
            uint256_t const t3 = aot::from_bool(!aot::nonzero(r11));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j16 = aot::nonzero(t4);
            uint256_t const m2 = s2;
            top[1] = uint256_t{0x0ull};
            top[2] = t1;
            top[3] = t2;
            top[4] = t1;
            top[5] = uint256_t{0x0ull};
            top[6] = m2;
            top[7] = t3;
            top += 7;
            if (j16) { MONAD_AOT_TAIL return b_8b1<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_8ae<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_8ae(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_8b1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x5a, 0xf1, 0x15, 0x80, 0x15, 0x61, 0x57}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x5a, 0xf1, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xf1, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            uint256_t const &s4 = top[-4];
            uint256_t const &s5 = top[-5];
            uint256_t const &s6 = top[-6];
            auto const c3 = aot::call<traits>(ctx, gas, t1, s1, s2, s3, s4, s5, s6, (aot::gas_of<traits>({0x15, 0x80, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::from_bool(!aot::nonzero(c3));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j8 = aot::nonzero(t3);
            top[-6] = t2;
            top += -6;
            if (j8) { MONAD_AOT_TAIL return b_8c3<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_8bc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_8bc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const k3_0 = uint256_t{0x0ull};
            uint256_t const k3_1 = uint256_t{0x0ull};
            ctx->gas_remaining = gas;
            runtime::returndatacopy<traits>(ctx, &k3_0, &k3_1, &t1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, t2);
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_8c3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x60, 0x51, 0x7f, 0x81, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x84, 0x92, 0x50, 0x73, 0x8f, 0x16, 0x91, 0x50, 0x63, 0x90, 0x60, 0x01, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x86, 0x5a, 0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}, 16, 6));
            if (MONAD_UNLIKELY(top - bottom < 16)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x60, 0x51, 0x7f, 0x81, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x84, 0x92, 0x50, 0x73, 0x8f, 0x16, 0x91, 0x50, 0x63, 0x90, 0x60, 0x01, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x86, 0x5a, 0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x70a0823100000000ull});
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t3 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const &s15 = top[-15];
            uint256_t const t4 = s15 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t5 = uint256_t{0x24ull} + t1;
            uint256_t const t6 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t7 = t5 - t6;
            uint256_t const t8 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k34_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r34;
            runtime::staticcall<traits>(ctx, &r34, &t8, &t4, &t6, &t7, &t6, &k34_5, (aot::gas_of<traits>({0x15, 0x80, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(r34));
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            bool const j39 = aot::nonzero(t10);
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-3] = m5;
            top[-2] = t4;
            top[-1] = uint256_t{0x70a08231ull};
            top[0] = t5;
            top[1] = t9;
            top += 1;
            if (j39) { MONAD_AOT_TAIL return b_931<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_92a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_92a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const k3_0 = uint256_t{0x0ull};
            uint256_t const k3_1 = uint256_t{0x0ull};
            ctx->gas_remaining = gas;
            runtime::returndatacopy<traits>(ctx, &k3_0, &k3_1, &t1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, t2);
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_931(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x60, 0x51, 0x3d, 0x60, 0x19, 0x60, 0x82, 0x01, 0x16, 0x82, 0x01, 0x80, 0x60, 0x52, 0x50, 0x81, 0x01, 0x90, 0x61, 0x91, 0x90, 0x61, 0x56}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x60, 0x51, 0x3d, 0x60, 0x19, 0x60, 0x82, 0x01, 0x16, 0x82, 0x01, 0x80, 0x60, 0x52, 0x50, 0x81, 0x01, 0x90, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t3 = t2 + uint256_t{0x1full};
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t5 = t1 + t4;
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t5);
            uint256_t const t6 = t1 + t2;
            top[-3] = uint256_t{0x955ull};
            top[-2] = t6;
            top[-1] = t1;
            top += -1;
            MONAD_AOT_TAIL return b_36b7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_955(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x95full};
            top[0] = m1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_373e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_95f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x50, 0x80, 0x82, 0x10, 0x80, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x50, 0x80, 0x82, 0x10, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s0 < s1);
            bool const j8 = aot::nonzero(t1);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[0] = t1;
            if (j8) { MONAD_AOT_TAIL return b_976<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_96a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_96a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x61, 0x85, 0x81, 0x01, 0x82, 0x02, 0x04, 0x82, 0x11}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x61, 0x85, 0x81, 0x01, 0x82, 0x02, 0x04, 0x82, 0x11}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = uint256_t{0x2710ull} + s5;
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::mul(s1, t1);
            uint256_t const t3 = aot::udiv(t2, uint256_t{0x2710ull});
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = aot::from_bool(t3 < s2);
            top[0] = t4;
            MONAD_AOT_TAIL return b_976<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_976(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_9b1<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_97c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_97c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b01ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_9b1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x8c, 0x83, 0x61, 0x56}, 12, 4));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x8c, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0x9bbull};
            top[2] = m11;
            top[3] = m1;
            top += 3;
            MONAD_AOT_TAIL return b_1dfb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_9bb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x80, 0x8d, 0x16, 0x5f, 0x90, 0x81, 0x52, 0x60, 0x60, 0x52, 0x60, 0x90, 0x20, 0x54, 0x61, 0x85, 0x01, 0x52, 0x8d, 0x16, 0x15, 0x80, 0x15, 0x61, 0x57}, 13, 4));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x80, 0x8d, 0x16, 0x5f, 0x90, 0x81, 0x52, 0x60, 0x60, 0x52, 0x60, 0x90, 0x20, 0x54, 0x61, 0x85, 0x01, 0x52, 0x8d, 0x16, 0x15, 0x80, 0x15, 0x61, 0x57}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = s11 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x5ull});
            uint256_t const t2 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = s2 + uint256_t{0x100ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const &s12 = top[-12];
            uint256_t const t5 = s12 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            bool const j26 = aot::nonzero(t7);
            top[1] = t6;
            top += 1;
            if (j26) { MONAD_AOT_TAIL return b_9fd<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_9f1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9f1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x61, 0x83, 0x01, 0x51, 0x60, 0x1c, 0x15, 0x15}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x61, 0x83, 0x01, 0x51, 0x60, 0x1c, 0x15, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x100ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = aot::shr_c<255>(t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            top[0] = t5;
            MONAD_AOT_TAIL return b_9fd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_9fd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_a38<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_a03<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a03(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b0full});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_a38(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x83, 0x61, 0x01, 0x51, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x83, 0x61, 0x01, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0x100ull} + s2;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            top[1] = uint256_t{0xa46ull};
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_20ef<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_a46(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x80, 0x86, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x80, 0x86, 0x01, 0x92, 0x90, 0x92, 0x52, 0x73, 0x8e, 0x16, 0x5f, 0x90, 0x81, 0x52, 0x60, 0x90, 0x92, 0x52, 0x90, 0x81, 0x90, 0x20, 0x54, 0x60, 0x85, 0x01, 0x81, 0x90, 0x52, 0x66, 0x60, 0x82, 0x90, 0x1c, 0x81, 0x16, 0x60, 0x80, 0x84, 0x16, 0x91, 0x90, 0x91, 0x1b, 0x60, 0x88, 0x01, 0x52, 0x60, 0x83, 0x90, 0x1c, 0x82, 0x16, 0x93, 0x83, 0x90, 0x1c, 0x81, 0x16, 0x93, 0x90, 0x93, 0x1b, 0x60, 0x80, 0x88, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x83, 0x90, 0x1c, 0x90, 0x91, 0x16, 0x90, 0x82, 0x90, 0x1c, 0x83, 0x16, 0x1b, 0x60, 0x86, 0x01, 0x52, 0x60, 0x81, 0x90, 0x1c, 0x60, 0x91, 0x82, 0x1c, 0x92, 0x83, 0x16, 0x1b, 0x90, 0x85, 0x01, 0x52, 0x91, 0x50, 0x8a, 0x15, 0x61, 0x57}, 14, 5));
            if (MONAD_UNLIKELY(top - bottom < 14)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x80, 0x86, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x80, 0x86, 0x01, 0x92, 0x90, 0x92, 0x52, 0x73, 0x8e, 0x16, 0x5f, 0x90, 0x81, 0x52, 0x60, 0x90, 0x92, 0x52, 0x90, 0x81, 0x90, 0x20, 0x54, 0x60, 0x85, 0x01, 0x81, 0x90, 0x52, 0x66, 0x60, 0x82, 0x90, 0x1c, 0x81, 0x16, 0x60, 0x80, 0x84, 0x16, 0x91, 0x90, 0x91, 0x1b, 0x60, 0x88, 0x01, 0x52, 0x60, 0x83, 0x90, 0x1c, 0x82, 0x16, 0x93, 0x83, 0x90, 0x1c, 0x81, 0x16, 0x93, 0x90, 0x93, 0x1b, 0x60, 0x80, 0x88, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x83, 0x90, 0x1c, 0x90, 0x91, 0x16, 0x90, 0x82, 0x90, 0x1c, 0x83, 0x16, 0x1b, 0x60, 0x86, 0x01, 0x52, 0x60, 0x81, 0x90, 0x1c, 0x60, 0x91, 0x82, 0x1c, 0x92, 0x83, 0x16, 0x1b, 0x90, 0x85, 0x01, 0x52, 0x91, 0x50, 0x8a, 0x15, 0x61, 0x57}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s4 + uint256_t{0x40ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const t2 = s4 + uint256_t{0x20ull};
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t2, s1);
            uint256_t const &s13 = top[-13];
            uint256_t const t3 = s13 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x7ull});
            uint256_t const t4 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t5 = aot::sload<traits>(ctx, gas, t4);
            uint256_t const t6 = s4 + uint256_t{0xe0ull};
            aot::mstore<traits>(ctx, gas, t6, t5);
            uint256_t const t7 = aot::shr_c<8>(t5);
            uint256_t const t8 = uint256_t{0xffffffffffffffull} & t7;
            uint256_t const t9 = t5 & uint256_t{0xffull};
            uint256_t const t10 = aot::shl(t9, t8);
            uint256_t const t11 = s4 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t11, t10);
            uint256_t const t12 = aot::shr_c<72>(t5);
            uint256_t const t13 = uint256_t{0xffffffffffffffull} & t12;
            uint256_t const t14 = aot::shr_c<64>(t5);
            uint256_t const t15 = uint256_t{0xffull} & t14;
            uint256_t const t16 = aot::shl(t15, t13);
            uint256_t const t17 = s4 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t17, t16);
            uint256_t const t18 = aot::shr_c<136>(t5);
            uint256_t const t19 = uint256_t{0xffffffffffffffull} & t18;
            uint256_t const t20 = aot::shr_c<128>(t5);
            uint256_t const t21 = uint256_t{0xffull} & t20;
            uint256_t const t22 = aot::shl(t21, t19);
            uint256_t const t23 = s4 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t23, t22);
            uint256_t const t24 = aot::shr_c<200>(t5);
            uint256_t const t25 = aot::shr_c<192>(t5);
            uint256_t const t26 = t25 & uint256_t{0xffull};
            uint256_t const t27 = aot::shl(t26, t24);
            uint256_t const t28 = s4 + uint256_t{0xc0ull};
            aot::mstore<traits>(ctx, gas, t28, t27);
            uint256_t const &s12 = top[-12];
            uint256_t const t29 = aot::from_bool(!aot::nonzero(s12));
            bool const j121 = aot::nonzero(t29);
            top[-3] = t25;
            top += -2;
            if (j121) { MONAD_AOT_TAIL return b_d03<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_aea<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_aea(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x60, 0x01, 0x51, 0x90, 0x50, 0x5f, 0x5f, 0x61, 0x8f, 0x8f, 0x8f, 0x88, 0x60, 0x01, 0x51, 0x61, 0x56}, 13, 8));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x60, 0x01, 0x51, 0x90, 0x50, 0x5f, 0x5f, 0x61, 0x8f, 0x8f, 0x8f, 0x88, 0x60, 0x01, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0xe0ull} + s2;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = uint256_t{0x20ull} + s2;
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[0] = t2;
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top[3] = uint256_t{0xb02ull};
            top[4] = m12;
            top[5] = m11;
            top[6] = m10;
            top[7] = t4;
            top += 7;
            MONAD_AOT_TAIL return b_22fd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b02(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x50, 0x91, 0x50, 0x80, 0x5f, 0x03, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x50, 0x91, 0x50, 0x80, 0x5f, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            bool const j9 = aot::nonzero(t1);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const m0 = s0;
            top[-3] = m1;
            top[-2] = m0;
            top += -2;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xbbd); }
            MONAD_AOT_TAIL return b_b0e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b0e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x82, 0x13, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x82, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s1));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j5 = aot::nonzero(t2);
            if (j5) { MONAD_AOT_TAIL return b_b3f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_b16<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b16(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x82, 0x86, 0x60, 0x01, 0x51, 0x60, 0x61, 0x56}, 5, 5));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x82, 0x86, 0x60, 0x01, 0x51, 0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = uint256_t{0x60ull} + s4;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0xb25ull};
            top[2] = m1;
            top[3] = t2;
            top[4] = uint256_t{0x1ull};
            top += 4;
            MONAD_AOT_TAIL return b_2844<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b25(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x85, 0x60, 0x01, 0x81, 0x81, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}, 5, 6));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x85, 0x60, 0x01, 0x81, 0x81, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = uint256_t{0x60ull} + s4;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = m1;
            top[2] = t1;
            top[3] = uint256_t{0xb37ull};
            top[4] = m1;
            top[5] = t2;
            top += 5;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b37(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x52, 0x50, 0x61, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x52, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s1, s0);
            top += -3;
            MONAD_AOT_TAIL return b_b77<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b3f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x83, 0x61, 0x56}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0xb56ull};
            top[2] = uint256_t{0xb4bull};
            top[3] = m1;
            top += 3;
            MONAD_AOT_TAIL return b_3641<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b4b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x86, 0x60, 0x01, 0x51, 0x5f, 0x61, 0x56}, 7, 3));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x86, 0x60, 0x01, 0x51, 0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = uint256_t{0x60ull} + s6;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            top[1] = t2;
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_2844<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b56(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x5f, 0x03, 0x85, 0x60, 0x01, 0x51, 0x11, 0x61, 0x57}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x5f, 0x03, 0x85, 0x60, 0x01, 0x51, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = uint256_t{0x0ull} - s1;
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = uint256_t{0x60ull} + s4;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = aot::from_bool(t1 < t3);
            bool const j10 = aot::nonzero(t4);
            if (j10) { MONAD_AOT_TAIL return b_b69<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_b64<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b64(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_b71<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b69(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x85, 0x01, 0x51, 0x82, 0x01}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x85, 0x01, 0x51, 0x82, 0x01}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s4 + uint256_t{0x60ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = s1 + t2;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_b71<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b71(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x86, 0x01, 0x52}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x86, 0x01, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = s5 + uint256_t{0x60ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            top += -1;
            MONAD_AOT_TAIL return b_b77<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b77(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x85, 0x01, 0x51, 0x61, 0x90, 0x60, 0x60, 0x5f, 0x61, 0x56}, 5, 6));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x85, 0x01, 0x51, 0x61, 0x90, 0x60, 0x60, 0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s4 + uint256_t{0x60ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            top[1] = uint256_t{0xb8aull};
            top[2] = t2;
            top[3] = uint256_t{0x38ull};
            top[4] = uint256_t{0x8ull};
            top[5] = uint256_t{0x0ull};
            top += 5;
            MONAD_AOT_TAIL return b_28b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b8a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x86, 0x01, 0x80, 0x51, 0x7f, 0x16, 0x82, 0x17, 0x90, 0x52, 0x93, 0x50, 0x61, 0x56}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x86, 0x01, 0x80, 0x51, 0x7f, 0x16, 0x82, 0x17, 0x90, 0x52, 0x93, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = s5 + uint256_t{0xe0ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = uint256_t{0x0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} & t2;
            uint256_t const &s0 = top[0];
            uint256_t const t4 = s0 | t3;
            aot::mstore<traits>(ctx, gas, t1, t4);
            uint256_t const m0 = s0;
            top[-4] = m0;
            top += -1;
            MONAD_AOT_TAIL return b_cbf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_bc6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x81, 0x86, 0x60, 0x01, 0x51, 0x60, 0x61, 0x56}, 5, 5));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x81, 0x86, 0x60, 0x01, 0x51, 0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = uint256_t{0x80ull} + s4;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0xbd5ull};
            top[2] = m0;
            top[3] = t2;
            top[4] = uint256_t{0x1ull};
            top += 4;
            MONAD_AOT_TAIL return b_2844<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c14(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc21);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_c44(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b06ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_cbf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x60, 0x01, 0x51, 0x83, 0x03, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x60, 0x01, 0x51, 0x83, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = uint256_t{0xe0ull} + s4;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = s2 - t2;
            bool const j8 = aot::nonzero(t3);
            if (j8) { MONAD_AOT_TAIL return b_d00<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_ccb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ccb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2affull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d00(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top += -2;
            MONAD_AOT_TAIL return b_d03<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d03(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x89, 0x15, 0x61, 0x57}, 10, 2));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x89, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s9 = top[-9];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s9));
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_f21<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_d0a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d0a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x60, 0x01, 0x51, 0x90, 0x50, 0x5f, 0x5f, 0x61, 0x8f, 0x8f, 0x8e, 0x88, 0x60, 0x01, 0x51, 0x61, 0x56}, 13, 8));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x60, 0x01, 0x51, 0x90, 0x50, 0x5f, 0x5f, 0x61, 0x8f, 0x8f, 0x8e, 0x88, 0x60, 0x01, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0xe0ull} + s2;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = uint256_t{0x40ull} + s2;
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[0] = t2;
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top[3] = uint256_t{0xd22ull};
            top[4] = m12;
            top[5] = m11;
            top[6] = m9;
            top[7] = t4;
            top += 7;
            MONAD_AOT_TAIL return b_29d9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d22(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x50, 0x91, 0x50, 0x80, 0x5f, 0x03, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x50, 0x91, 0x50, 0x80, 0x5f, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            bool const j9 = aot::nonzero(t1);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const m0 = s0;
            top[-3] = m1;
            top[-2] = m0;
            top += -2;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xde2); }
            MONAD_AOT_TAIL return b_d2e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d2e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x82, 0x13, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x82, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s1));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j5 = aot::nonzero(t2);
            if (j5) { MONAD_AOT_TAIL return b_d5f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_d36<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d36(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x82, 0x86, 0x60, 0x01, 0x51, 0x60, 0x61, 0x56}, 5, 5));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x82, 0x86, 0x60, 0x01, 0x51, 0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = uint256_t{0xa0ull} + s4;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0xd45ull};
            top[2] = m1;
            top[3] = t2;
            top[4] = uint256_t{0x1ull};
            top += 4;
            MONAD_AOT_TAIL return b_2844<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d45(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x85, 0x60, 0x01, 0x81, 0x81, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}, 5, 6));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x85, 0x60, 0x01, 0x81, 0x81, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = uint256_t{0xa0ull} + s4;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = m1;
            top[2] = t1;
            top[3] = uint256_t{0xd57ull};
            top[4] = m1;
            top[5] = t2;
            top += 5;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d57(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x52, 0x50, 0x61, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x52, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s1, s0);
            top += -3;
            MONAD_AOT_TAIL return b_d97<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d5f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x83, 0x61, 0x56}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0xd76ull};
            top[2] = uint256_t{0xd6bull};
            top[3] = m1;
            top += 3;
            MONAD_AOT_TAIL return b_3641<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d6b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x86, 0x60, 0x01, 0x51, 0x5f, 0x61, 0x56}, 7, 3));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x86, 0x60, 0x01, 0x51, 0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = uint256_t{0xa0ull} + s6;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            top[1] = t2;
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_2844<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d76(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x5f, 0x03, 0x85, 0x60, 0x01, 0x51, 0x11, 0x61, 0x57}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x5f, 0x03, 0x85, 0x60, 0x01, 0x51, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = uint256_t{0x0ull} - s1;
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = uint256_t{0xa0ull} + s4;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = aot::from_bool(t1 < t3);
            bool const j10 = aot::nonzero(t4);
            if (j10) { MONAD_AOT_TAIL return b_d89<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_d84<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d84(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_d91<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d89(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x85, 0x01, 0x51, 0x82, 0x01}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x85, 0x01, 0x51, 0x82, 0x01}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s4 + uint256_t{0xa0ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = s1 + t2;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return b_d91<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d91(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x86, 0x01, 0x52}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x86, 0x01, 0x52}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = s5 + uint256_t{0xa0ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            top += -1;
            MONAD_AOT_TAIL return b_d97<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_d97(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x85, 0x01, 0x51, 0x61, 0x90, 0x60, 0x60, 0x60, 0x61, 0x56}, 5, 6));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x85, 0x01, 0x51, 0x61, 0x90, 0x60, 0x60, 0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s4 + uint256_t{0xa0ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            top[1] = uint256_t{0xdabull};
            top[2] = t2;
            top[3] = uint256_t{0x38ull};
            top[4] = uint256_t{0x8ull};
            top[5] = uint256_t{0x1ull};
            top += 5;
            MONAD_AOT_TAIL return b_28b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_dab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x86, 0x01, 0x80, 0x51, 0x7f, 0x16, 0x60, 0x83, 0x90, 0x1b, 0x17, 0x90, 0x52, 0x93, 0x50, 0x61, 0x56}, 6, 4));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x86, 0x01, 0x80, 0x51, 0x7f, 0x16, 0x60, 0x83, 0x90, 0x1b, 0x17, 0x90, 0x52, 0x93, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = s5 + uint256_t{0xe0ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0xffffffffffffffffull} & t2;
            uint256_t const &s0 = top[0];
            uint256_t const t4 = aot::shl_c<128>(s0);
            uint256_t const t5 = t4 | t3;
            aot::mstore<traits>(ctx, gas, t1, t5);
            uint256_t const m0 = s0;
            top[-4] = m0;
            top += -1;
            MONAD_AOT_TAIL return b_edd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_deb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x81, 0x86, 0x60, 0x01, 0x51, 0x60, 0x61, 0x56}, 5, 5));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x81, 0x86, 0x60, 0x01, 0x51, 0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = uint256_t{0xc0ull} + s4;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0xdfaull};
            top[2] = m0;
            top[3] = t2;
            top[4] = uint256_t{0x1ull};
            top += 4;
            MONAD_AOT_TAIL return b_2844<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e39(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xe46);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e69(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b07ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_edd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x60, 0x01, 0x51, 0x83, 0x03, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x60, 0x01, 0x51, 0x83, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = uint256_t{0xe0ull} + s4;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = s2 - t2;
            bool const j8 = aot::nonzero(t3);
            if (j8) { MONAD_AOT_TAIL return b_f1e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_ee9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ee9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2affull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_f1e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top += -2;
            MONAD_AOT_TAIL return b_f21<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_f21(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x83, 0x01, 0x51, 0x73, 0x8d, 0x16, 0x5f, 0x90, 0x81, 0x52, 0x60, 0x60, 0x90, 0x81, 0x52, 0x60, 0x90, 0x91, 0x20, 0x91, 0x90, 0x91, 0x55, 0x83, 0x01, 0x51, 0x60, 0x84, 0x01, 0x51, 0x64, 0x91, 0x61, 0x91, 0x61, 0x56}, 12, 5));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x83, 0x01, 0x51, 0x73, 0x8d, 0x16, 0x5f, 0x90, 0x81, 0x52, 0x60, 0x60, 0x90, 0x81, 0x52, 0x60, 0x90, 0x91, 0x20, 0x91, 0x90, 0x91, 0x55, 0x83, 0x01, 0x51, 0x60, 0x84, 0x01, 0x51, 0x64, 0x91, 0x61, 0x91, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0xe0ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s11 = top[-11];
            uint256_t const t3 = s11 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x7ull});
            uint256_t const t4 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            aot::sstore<traits>(ctx, gas, t4, t2, (aot::gas_of<traits>({0x83, 0x01, 0x51, 0x60, 0x84, 0x01, 0x51, 0x64, 0x91, 0x61, 0x91, 0x61, 0x56}) + 0));
            uint256_t const t5 = s2 + uint256_t{0x20ull};
            uint256_t const t6 = aot::mload<traits>(ctx, gas, t5);
            uint256_t const t7 = s2 + uint256_t{0x60ull};
            uint256_t const t8 = aot::mload<traits>(ctx, gas, t7);
            top[1] = uint256_t{0xe8d4a51000ull};
            top[2] = uint256_t{0xf69ull};
            top[3] = t6;
            top[4] = t8;
            top += 4;
            MONAD_AOT_TAIL return b_3751<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f69(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0xf73ull};
            top[0] = m1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_3768<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_f73(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x94, 0x50, 0x6f, 0x85, 0x11, 0x80, 0x15, 0x61, 0x57}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x94, 0x50, 0x6f, 0x85, 0x11, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xffffffffffffffffull, 0x7fffffffffffffffull, 0x0ull, 0x0ull} < s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            top[-5] = m0;
            top[0] = t1;
            if (j9) { MONAD_AOT_TAIL return b_f93<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_f8f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f8f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x5f, 0x8b, 0x13}, 12, 1));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x5f, 0x8b, 0x13}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s11));
            top[0] = t1;
            MONAD_AOT_TAIL return b_f93<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_f93(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_fce<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_f99<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f99(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b06ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x83, 0x60, 0x01, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}, 5, 4));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x83, 0x60, 0x01, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0x80ull} + s2;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[1] = uint256_t{0xfdeull};
            top[2] = m4;
            top[3] = t2;
            top += 3;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_fde(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x50, 0x82, 0x60, 0x01, 0x51, 0x85, 0x11, 0x15, 0x61, 0x57}, 6, 1));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x50, 0x82, 0x60, 0x01, 0x51, 0x85, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = uint256_t{0x80ull} + s3;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s5 = top[-5];
            uint256_t const t3 = aot::from_bool(t2 < s5);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j11 = aot::nonzero(t4);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top += -1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1014); }
            MONAD_AOT_TAIL return b_fed<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_fed(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x85, 0x61, 0x85, 0x60, 0x01, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}, 5, 6));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x85, 0x61, 0x85, 0x60, 0x01, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0x80ull} + s2;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[1] = uint256_t{0x1ull};
            top[2] = m4;
            top[3] = uint256_t{0x1001ull};
            top[4] = uint256_t{0x2710ull};
            top[5] = t2;
            top += 5;
            MONAD_AOT_TAIL return b_3751<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1001(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x100bull};
            top[0] = m1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_3768<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_100b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x1b, 0x94, 0x50, 0x61, 0x56}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x1b, 0x94, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl(s1, s0);
            top[-6] = t1;
            top += -2;
            MONAD_AOT_TAIL return b_1056<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1021(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x83, 0x01, 0x51, 0x60, 0x90, 0x61, 0x61, 0x88, 0x61, 0x56}, 5, 6));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x83, 0x01, 0x51, 0x60, 0x90, 0x61, 0x61, 0x88, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0x80ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[1] = uint256_t{0x1ull};
            top[2] = t2;
            top[3] = uint256_t{0x1034ull};
            top[4] = uint256_t{0x2710ull};
            top[5] = m4;
            top += 5;
            MONAD_AOT_TAIL return b_3751<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1051(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x94, 0x50}, 5, 1));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x94, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-4] = uint256_t{0x4e20ull};
            MONAD_AOT_TAIL return b_1056<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1056(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x64, 0x83, 0x60, 0x01, 0x51, 0x84, 0x60, 0x01, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x64, 0x83, 0x60, 0x01, 0x51, 0x84, 0x60, 0x01, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0x40ull} + s2;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = uint256_t{0xa0ull} + s2;
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            top[1] = uint256_t{0xe8d4a51000ull};
            top[2] = uint256_t{0x1070ull};
            top[3] = t2;
            top[4] = t4;
            top += 4;
            MONAD_AOT_TAIL return b_3751<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1070(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x107aull};
            top[0] = m1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_3768<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_107a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x93, 0x50, 0x6f, 0x84, 0x11, 0x80, 0x15, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x93, 0x50, 0x6f, 0x84, 0x11, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xffffffffffffffffull, 0x7fffffffffffffffull, 0x0ull, 0x0ull} < s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            top[-4] = m0;
            top[0] = t1;
            if (j9) { MONAD_AOT_TAIL return b_109a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1096<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1096(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x5f, 0x8a, 0x13}, 11, 1));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x5f, 0x8a, 0x13}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s10 = top[-10];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s10));
            top[0] = t1;
            MONAD_AOT_TAIL return b_109a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_109a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_10d5<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_10a0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10a0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b07ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_10d5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x83, 0x60, 0x01, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x83, 0x60, 0x01, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0xc0ull} + s2;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[1] = uint256_t{0x10e5ull};
            top[2] = m3;
            top[3] = t2;
            top += 3;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_10e5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x82, 0x60, 0x01, 0x51, 0x84, 0x11, 0x15, 0x61, 0x57}, 5, 1));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x82, 0x60, 0x01, 0x51, 0x84, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = uint256_t{0xc0ull} + s3;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s4 = top[-4];
            uint256_t const t3 = aot::from_bool(t2 < s4);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j11 = aot::nonzero(t4);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x111b); }
            MONAD_AOT_TAIL return b_10f4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10f4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x84, 0x61, 0x85, 0x60, 0x01, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}, 4, 6));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x84, 0x61, 0x85, 0x60, 0x01, 0x51, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0xc0ull} + s2;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[1] = uint256_t{0x1ull};
            top[2] = m3;
            top[3] = uint256_t{0x1108ull};
            top[4] = uint256_t{0x2710ull};
            top[5] = t2;
            top += 5;
            MONAD_AOT_TAIL return b_3751<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1108(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x1112ull};
            top[0] = m1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_3768<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1112(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x1b, 0x93, 0x50, 0x61, 0x56}, 6, 0));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x1b, 0x93, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl(s1, s0);
            top[-5] = t1;
            top += -2;
            MONAD_AOT_TAIL return b_115d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1128(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x83, 0x01, 0x51, 0x60, 0x90, 0x61, 0x61, 0x87, 0x61, 0x56}, 4, 6));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x83, 0x01, 0x51, 0x60, 0x90, 0x61, 0x61, 0x87, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0xc0ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[1] = uint256_t{0x1ull};
            top[2] = t2;
            top[3] = uint256_t{0x113bull};
            top[4] = uint256_t{0x2710ull};
            top[5] = m3;
            top += 5;
            MONAD_AOT_TAIL return b_3751<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1158(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x93, 0x50}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x93, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-3] = uint256_t{0x4e20ull};
            MONAD_AOT_TAIL return b_115d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_115d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x82, 0x15, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x82, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s1));
            bool const j5 = aot::nonzero(t1);
            top[1] = uint256_t{0x0ull};
            top += 1;
            if (j5) { MONAD_AOT_TAIL return b_120b<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1165<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1165(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x61, 0x61, 0x84, 0x61, 0x56}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x61, 0x61, 0x84, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = m2;
            top[2] = uint256_t{0x1171ull};
            top[3] = uint256_t{0x2710ull};
            top[4] = m1;
            top += 4;
            MONAD_AOT_TAIL return b_3751<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1171(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x117bull};
            top[0] = m1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_3768<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_117b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x5f, 0x8b, 0x13, 0x15, 0x61, 0x57}, 12, 1));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x5f, 0x8b, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s11));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j8 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (j8) { MONAD_AOT_TAIL return b_120b<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1186<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1186(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x84, 0x61, 0x01, 0x51, 0x90, 0x1c, 0x60, 0x16, 0x60, 0x14, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x84, 0x61, 0x01, 0x51, 0x90, 0x1c, 0x60, 0x16, 0x60, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = uint256_t{0x100ull} + s3;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = aot::shr_c<249>(t2);
            uint256_t const t4 = uint256_t{0x1ull} & t3;
            uint256_t const t5 = aot::from_bool(uint256_t{0x1ull} == t4);
            bool const j12 = aot::nonzero(t5);
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11a1); }
            MONAD_AOT_TAIL return b_119a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_119a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x2710ull};
            top += 1;
            MONAD_AOT_TAIL return b_11cb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_11cb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x50, 0x82, 0x81, 0x11, 0x15, 0x61, 0x57}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x50, 0x82, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(s0 < s1);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j8 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            top[-3] = m0;
            top += -1;
            if (j8) { MONAD_AOT_TAIL return b_120b<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_11d6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11d6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b03ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_120b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x84, 0x01, 0x51, 0x60, 0x1c, 0x64, 0x16, 0x62, 0x01, 0x42, 0x11, 0x15, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x84, 0x01, 0x51, 0x60, 0x1c, 0x64, 0x16, 0x62, 0x01, 0x42, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x100ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = aot::shr_c<58>(t2);
            uint256_t const t4 = uint256_t{0x1ffffffffull} & t3;
            uint256_t const t5 = uint256_t{0x15180ull} + t4;
            uint256_t const t6 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const t7 = aot::from_bool(t5 < t6);
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j15 = aot::nonzero(t8);
            if (j15) { MONAD_AOT_TAIL return b_1230<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1228<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1228(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x92, 0x50, 0x61, 0x56}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x92, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-2] = uint256_t{0x1ull};
            MONAD_AOT_TAIL return b_1234<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1230(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x92, 0x50}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x92, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-2] = uint256_t{0x0ull};
            MONAD_AOT_TAIL return b_1234<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1234(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x5f, 0x03, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x5f, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0x0ull} - s2;
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1352<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_123c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_123c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x60, 0x85, 0x61, 0x01, 0x51, 0x90, 0x1c, 0x16, 0x92, 0x50, 0x61, 0x60, 0x85, 0x61, 0x01, 0x51, 0x90, 0x1c, 0x16, 0x91, 0x50, 0x81, 0x83, 0x82, 0x11, 0x61, 0x57}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x60, 0x85, 0x61, 0x01, 0x51, 0x90, 0x1c, 0x16, 0x92, 0x50, 0x61, 0x60, 0x85, 0x61, 0x01, 0x51, 0x90, 0x1c, 0x16, 0x91, 0x50, 0x81, 0x83, 0x82, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = uint256_t{0x100ull} + s3;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = aot::shr_c<30>(t2);
            uint256_t const t4 = t3 & uint256_t{0x3fffull};
            uint256_t const t5 = uint256_t{0x100ull} + s3;
            uint256_t const t6 = aot::mload<traits>(ctx, gas, t5);
            uint256_t const t7 = aot::shr_c<44>(t6);
            uint256_t const t8 = t7 & uint256_t{0x3fffull};
            uint256_t const &s0 = top[0];
            uint256_t const t9 = aot::from_bool(t4 < s0);
            bool const j27 = aot::nonzero(t9);
            top[-2] = t4;
            top[-1] = t8;
            top[1] = t8;
            top += 1;
            if (j27) { MONAD_AOT_TAIL return b_126b<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1264<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1264(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x84, 0x03, 0x61, 0x56}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x84, 0x03, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s3 - s1;
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_126f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_126b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x82, 0x03}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x82, 0x03}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s1 - s3;
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_126f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_126f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x11, 0x61, 0x57}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < s0);
            bool const j3 = aot::nonzero(t1);
            top += -2;
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x127a); }
            MONAD_AOT_TAIL return b_1275<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1275(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_127d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_127d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x16, 0x92, 0x50, 0x82, 0x5f, 0x03, 0x61, 0x57}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x16, 0x92, 0x50, 0x82, 0x5f, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0xffull} & s0;
            uint256_t const t2 = uint256_t{0x0ull} - t1;
            bool const j9 = aot::nonzero(t2);
            top[-3] = t1;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return b_1352<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_128a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_128a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x60, 0x85, 0x61, 0x01, 0x51, 0x90, 0x1c, 0x16, 0x92, 0x50, 0x85, 0x60, 0x16, 0x83, 0x60, 0x16, 0x03, 0x61, 0x57}, 6, 4));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x60, 0x85, 0x61, 0x01, 0x51, 0x90, 0x1c, 0x16, 0x92, 0x50, 0x85, 0x60, 0x16, 0x83, 0x60, 0x16, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = uint256_t{0x100ull} + s3;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = aot::shr_c<219>(t2);
            uint256_t const t4 = t3 & uint256_t{0x7fffull};
            uint256_t const &s5 = top[-5];
            uint256_t const t5 = uint256_t{0x1ull} & s5;
            uint256_t const t6 = uint256_t{0x1ull} & t4;
            uint256_t const t7 = t6 - t5;
            bool const j19 = aot::nonzero(t7);
            top[-2] = t4;
            if (j19) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x12e5); }
            MONAD_AOT_TAIL return b_12a7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12a7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x83, 0x90, 0x1c, 0x92, 0x50, 0x81, 0x83, 0x60, 0x88, 0x90, 0x1c, 0x11, 0x61, 0x57}, 6, 4));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x83, 0x90, 0x1c, 0x92, 0x50, 0x81, 0x83, 0x60, 0x88, 0x90, 0x1c, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::shr_c<1>(s2);
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = aot::shr_c<1>(s5);
            uint256_t const t3 = aot::from_bool(t1 < t2);
            bool const j14 = aot::nonzero(t3);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-2] = t1;
            top[1] = m1;
            top += 1;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x12c5); }
            MONAD_AOT_TAIL return b_12ba<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12ba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x87, 0x90, 0x1c, 0x84, 0x03, 0x61, 0x56}, 7, 2));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x87, 0x90, 0x1c, 0x84, 0x03, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::shr_c<1>(s6);
            uint256_t const &s3 = top[-3];
            uint256_t const t2 = s3 - t1;
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_12cd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_12cd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x11, 0x61, 0x57}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < s0);
            bool const j3 = aot::nonzero(t1);
            top += -2;
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x12d8); }
            MONAD_AOT_TAIL return b_12d3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12d3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_12db<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_12db(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x16, 0x92, 0x50, 0x61, 0x56}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x16, 0x92, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0xffull} & s0;
            top[-3] = t1;
            top += -1;
            MONAD_AOT_TAIL return b_12ea<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_12ea(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x5f, 0x03, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x5f, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0x0ull} - s2;
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1352<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_12f2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12f2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x60, 0x85, 0x61, 0x01, 0x51, 0x90, 0x1c, 0x16, 0x92, 0x50, 0x84, 0x60, 0x16, 0x83, 0x60, 0x16, 0x03, 0x61, 0x57}, 5, 4));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x60, 0x85, 0x61, 0x01, 0x51, 0x90, 0x1c, 0x16, 0x92, 0x50, 0x84, 0x60, 0x16, 0x83, 0x60, 0x16, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = uint256_t{0x100ull} + s3;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = aot::shr_c<234>(t2);
            uint256_t const t4 = t3 & uint256_t{0x7fffull};
            uint256_t const &s4 = top[-4];
            uint256_t const t5 = uint256_t{0x1ull} & s4;
            uint256_t const t6 = uint256_t{0x1ull} & t4;
            uint256_t const t7 = t6 - t5;
            bool const j19 = aot::nonzero(t7);
            top[-2] = t4;
            if (j19) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x134d); }
            MONAD_AOT_TAIL return b_130f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_130f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x83, 0x90, 0x1c, 0x92, 0x50, 0x81, 0x83, 0x60, 0x87, 0x90, 0x1c, 0x11, 0x61, 0x57}, 5, 4));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x83, 0x90, 0x1c, 0x92, 0x50, 0x81, 0x83, 0x60, 0x87, 0x90, 0x1c, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::shr_c<1>(s2);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = aot::shr_c<1>(s4);
            uint256_t const t3 = aot::from_bool(t1 < t2);
            bool const j14 = aot::nonzero(t3);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-2] = t1;
            top[1] = m1;
            top += 1;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x132d); }
            MONAD_AOT_TAIL return b_1322<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1322(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x86, 0x90, 0x1c, 0x84, 0x03, 0x61, 0x56}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x86, 0x90, 0x1c, 0x84, 0x03, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = aot::shr_c<1>(s5);
            uint256_t const &s3 = top[-3];
            uint256_t const t2 = s3 - t1;
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_1335<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1335(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x11, 0x61, 0x57}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < s0);
            bool const j3 = aot::nonzero(t1);
            top += -2;
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1340); }
            MONAD_AOT_TAIL return b_133b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_133b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_1343<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1343(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x16, 0x92, 0x50, 0x61, 0x56}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x16, 0x92, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0xffull} & s0;
            top[-3] = t1;
            top += -1;
            MONAD_AOT_TAIL return b_1352<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1352(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x60, 0x03, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x60, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0x1ull} - s2;
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_14d7<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_135b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_135b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x73, 0x8d, 0x16, 0x5f, 0x90, 0x81, 0x52, 0x60, 0x60, 0x52, 0x60, 0x90, 0x20, 0x54, 0x61, 0x90, 0x82, 0x61, 0x56}, 13, 4));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x73, 0x8d, 0x16, 0x5f, 0x90, 0x81, 0x52, 0x60, 0x60, 0x52, 0x60, 0x90, 0x20, 0x54, 0x61, 0x90, 0x82, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s12 = top[-12];
            uint256_t const t1 = s12 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x6ull});
            uint256_t const t2 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x1389ull};
            top[2] = t3;
            top[3] = m0;
            top += 3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2ce8);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_13a0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x67, 0x84, 0x60, 0x01, 0x51, 0x11}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x67, 0x84, 0x60, 0x01, 0x51, 0x11}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = uint256_t{0x40ull} + s4;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t2);
            top[0] = t3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x13b0);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_13b6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b04ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_13f6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b05ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_14d7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x84, 0x60, 0x01, 0x51, 0x90, 0x1b, 0x60, 0x85, 0x60, 0x01, 0x51, 0x90, 0x1b, 0x85, 0x61, 0x01, 0x51, 0x7f, 0x16, 0x17, 0x17, 0x84, 0x61, 0x01, 0x81, 0x81, 0x52, 0x50, 0x50}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x84, 0x60, 0x01, 0x51, 0x90, 0x1b, 0x60, 0x85, 0x60, 0x01, 0x51, 0x90, 0x1b, 0x85, 0x61, 0x01, 0x51, 0x7f, 0x16, 0x17, 0x17, 0x84, 0x61, 0x01, 0x81, 0x81, 0x52, 0x50, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = uint256_t{0x40ull} + s3;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = aot::shl_c<155>(t2);
            uint256_t const t4 = uint256_t{0x20ull} + s3;
            uint256_t const t5 = aot::mload<traits>(ctx, gas, t4);
            uint256_t const t6 = aot::shl_c<91>(t5);
            uint256_t const t7 = uint256_t{0x100ull} + s3;
            uint256_t const t8 = aot::mload<traits>(ctx, gas, t7);
            uint256_t const t9 = uint256_t{0xffffffffffffffffull, 0x7ffffffull, 0x0ull, 0xfffffffffc000000ull} & t8;
            uint256_t const t10 = t9 | t6;
            uint256_t const t11 = t10 | t3;
            uint256_t const t12 = uint256_t{0x100ull} + s3;
            aot::mstore<traits>(ctx, gas, t12, t11);
            MONAD_AOT_TAIL return b_151e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_151e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x5f, 0x8b, 0x12, 0x80, 0x61, 0x57}, 12, 2));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x5f, 0x8b, 0x12, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = aot::from_bool(slt(s11, uint256_t{0x0ull}));
            bool const j7 = aot::nonzero(t1);
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return b_152c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1528<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1528(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x5f, 0x8a, 0x13}, 11, 1));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x5f, 0x8a, 0x13}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s10 = top[-10];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s10));
            top[0] = t1;
            MONAD_AOT_TAIL return b_152c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_152c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_1558<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1533<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1533(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x82, 0x51, 0x7f, 0x12}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x82, 0x51, 0x7f, 0x12}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const t2 = aot::from_bool(slt(uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull}, t1));
            top[0] = t2;
            MONAD_AOT_TAIL return b_1558<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1558(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_1787<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_155e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_155e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x51, 0x5f, 0x12, 0x15, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x51, 0x5f, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const t2 = aot::from_bool(slt(uint256_t{0x0ull}, t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return b_1612<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1567<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1567(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x73, 0x8d, 0x16, 0x01, 0x61, 0x57}, 12, 3));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x73, 0x8d, 0x16, 0x01, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = s11 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = t1 + uint256_t{0x1111111111111112ull, 0x1111111111111111ull, 0xffffffff11111111ull, 0xffffffffffffffffull};
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x15d6); }
            MONAD_AOT_TAIL return b_15a4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_15a4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x73, 0x8a, 0x16, 0x15, 0x61, 0x57}, 9, 3));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x73, 0x8a, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = s8 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j6 = aot::nonzero(t2);
            top[1] = uint256_t{0x15d1ull};
            top += 1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x15c8); }
            MONAD_AOT_TAIL return b_15c3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_15c3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x89, 0x61, 0x56}, 10, 2));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x89, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[1] = m9;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x15ca);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_15d1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_1787<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1604(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x8a, 0x61, 0x56}, 11, 2));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[1] = m10;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x160b);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1612(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x8a, 0x13, 0x61, 0x57}, 10, 2));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x8a, 0x13, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s9 = top[-9];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s9));
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_161f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_161a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_161a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_1621<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_161f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x89}, 10, 1));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x89}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[1] = m9;
            top += 1;
            MONAD_AOT_TAIL return b_1621<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1621(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x5f, 0x8b, 0x12, 0x15, 0x61, 0x57}, 12, 1));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x5f, 0x8b, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = aot::from_bool(slt(s11, uint256_t{0x0ull}));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j8 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (j8) { MONAD_AOT_TAIL return b_1635<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_162c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_162c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x8a, 0x5f, 0x03, 0x91, 0x50, 0x61, 0x56}, 11, 2));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x8a, 0x5f, 0x03, 0x91, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s10 = top[-10];
            uint256_t const t1 = uint256_t{0x0ull} - s10;
            top[-1] = t1;
            MONAD_AOT_TAIL return b_1639<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1635(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x91, 0x50}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x91, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-1] = uint256_t{0x0ull};
            MONAD_AOT_TAIL return b_1639<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1639(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x82, 0x11, 0x80, 0x15, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x82, 0x11, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(uint256_t{0x0ull} < s1);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return b_1647<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1643<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1643(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x5f, 0x81, 0x11}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x5f, 0x81, 0x11}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(uint256_t{0x0ull} < s1);
            top[0] = t1;
            MONAD_AOT_TAIL return b_1647<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1647(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_167e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_164e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_164e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x87, 0x73, 0x16, 0x89, 0x73, 0x16, 0x14}, 10, 2));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x87, 0x73, 0x16, 0x89, 0x73, 0x16, 0x14}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s8;
            uint256_t const &s9 = top[-9];
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s9;
            uint256_t const t3 = aot::from_bool(t2 == t1);
            top[0] = t3;
            MONAD_AOT_TAIL return b_167e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_167e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_16f4<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1684<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1684(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x73, 0x8d, 0x16, 0x01, 0x61, 0x57}, 12, 3));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x73, 0x8d, 0x16, 0x01, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = s11 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = t1 + uint256_t{0x1111111111111112ull, 0x1111111111111111ull, 0xffffffff11111111ull, 0xffffffffffffffffull};
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return b_16d3<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_16c1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_16c1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x89, 0x61, 0x83, 0x85, 0x61, 0x56}, 9, 6));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x89, 0x61, 0x83, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0x15d1ull};
            top[2] = m8;
            top[3] = uint256_t{0x16ceull};
            top[4] = m0;
            top[5] = m1;
            top += 5;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_16ce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_2d8f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_16d3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x83, 0x61, 0x56}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0x16ddull};
            top[2] = m0;
            top[3] = m1;
            top += 3;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_16dd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x50, 0x61, 0x8c, 0x83, 0x61, 0x56}, 13, 3));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x50, 0x61, 0x8c, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            top[-2] = m0;
            top[0] = uint256_t{0x16e9ull};
            top[1] = m12;
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_2dd8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_16e9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x8c, 0x8a, 0x84, 0x61, 0x56}, 12, 5));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x8c, 0x8a, 0x84, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0x15d1ull};
            top[2] = m11;
            top[3] = m8;
            top[4] = m1;
            top += 4;
            MONAD_AOT_TAIL return b_304c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_16f4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x73, 0x8d, 0x16, 0x01, 0x61, 0x57}, 12, 3));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x73, 0x8d, 0x16, 0x01, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = s11 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = t1 + uint256_t{0x1111111111111112ull, 0x1111111111111111ull, 0xffffffff11111111ull, 0xffffffffffffffffull};
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return b_1751<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1732<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1732(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s1));
            bool const j3 = aot::nonzero(t1);
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1741); }
            MONAD_AOT_TAIL return b_1738<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1738(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x89, 0x83, 0x61, 0x56}, 9, 4));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x89, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0x1741ull};
            top[2] = m8;
            top[3] = m1;
            top += 3;
            MONAD_AOT_TAIL return b_2d8f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1748(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x88, 0x82, 0x61, 0x56}, 8, 4));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x88, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x15d1ull};
            top[2] = m7;
            top[3] = m0;
            top += 3;
            MONAD_AOT_TAIL return b_2d8f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1751(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s1));
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_176c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1758<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1758(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x8c, 0x83, 0x61, 0x56}, 12, 4));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x8c, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0x1761ull};
            top[2] = m11;
            top[3] = m1;
            top += 3;
            MONAD_AOT_TAIL return b_2dd8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_176c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_1787<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1773<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1773(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x8c, 0x82, 0x61, 0x56}, 12, 4));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x8c, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x177cull};
            top[2] = m11;
            top[3] = m0;
            top += 3;
            MONAD_AOT_TAIL return b_2dd8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_177c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x8c, 0x89, 0x83, 0x61, 0x56}, 12, 5));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x8c, 0x89, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x1787ull};
            top[2] = m11;
            top[3] = m7;
            top[4] = m0;
            top += 4;
            MONAD_AOT_TAIL return b_304c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1787(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x80, 0x8d, 0x16, 0x90, 0x8e, 0x16, 0x15, 0x61, 0x57}, 13, 3));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x80, 0x8d, 0x16, 0x90, 0x8e, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = s11 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const &s12 = top[-12];
            uint256_t const t2 = s12 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j10 = aot::nonzero(t3);
            top[1] = t1;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return b_17ad<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_17a8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_17a8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x8d, 0x61, 0x56}, 14, 2));
            if (MONAD_UNLIKELY(top - bottom < 14)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x8d, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s13 = top[-13];
            uint256_t const m13 = s13;
            top[1] = m13;
            top += 1;
            MONAD_AOT_TAIL return b_17af<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_17ad(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x33}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x33}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_17af<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_17af(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x16, 0x7f, 0x8d, 0x8d, 0x8d, 0x8d, 0x89, 0x60, 0x01, 0x51, 0x8a, 0x61, 0x01, 0x51, 0x60, 0x51, 0x61, 0x96, 0x95, 0x94, 0x93, 0x92, 0x91, 0x90, 0x95, 0x86, 0x52, 0x60, 0x86, 0x01, 0x94, 0x90, 0x94, 0x52, 0x73, 0x92, 0x83, 0x16, 0x60, 0x86, 0x01, 0x52, 0x91, 0x16, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x90, 0x56}, 13, 10));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x16, 0x7f, 0x8d, 0x8d, 0x8d, 0x8d, 0x89, 0x60, 0x01, 0x51, 0x8a, 0x61, 0x01, 0x51, 0x60, 0x51, 0x61, 0x96, 0x95, 0x94, 0x93, 0x92, 0x91, 0x90, 0x95, 0x86, 0x52, 0x60, 0x86, 0x01, 0x94, 0x90, 0x94, 0x52, 0x73, 0x92, 0x83, 0x16, 0x60, 0x86, 0x01, 0x52, 0x91, 0x16, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s0;
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = uint256_t{0xe0ull} + s4;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = uint256_t{0x100ull} + s4;
            uint256_t const t5 = aot::mload<traits>(ctx, gas, t4);
            uint256_t const t6 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s12 = top[-12];
            aot::mstore<traits>(ctx, gas, t6, s12);
            uint256_t const t7 = t6 + uint256_t{0x20ull};
            uint256_t const &s11 = top[-11];
            aot::mstore<traits>(ctx, gas, t7, s11);
            uint256_t const &s10 = top[-10];
            uint256_t const t8 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s10;
            uint256_t const t9 = t6 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t9, t8);
            uint256_t const &s9 = top[-9];
            uint256_t const t10 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s9;
            uint256_t const t11 = t6 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t11, t10);
            uint256_t const t12 = t6 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t12, t3);
            uint256_t const t13 = t6 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t13, t5);
            uint256_t const t14 = uint256_t{0xc0ull} + t6;
            top[0] = t1;
            top[1] = uint256_t{0xe6f29e571ad78d15ull, 0xffe66759d5c24513ull, 0x84ced7461bf4deacull, 0x4d93b232a24e82b2ull};
            top[2] = t14;
            top += 2;
            MONAD_AOT_TAIL return b_1841<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1841(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa3, 0x82, 0x60, 0x01, 0x51, 0x94, 0x50, 0x82, 0x60, 0x01, 0x51, 0x93, 0x50, 0x50, 0x50, 0x50, 0x98, 0x50, 0x98, 0x96, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}, 18, 2));
            if (MONAD_UNLIKELY(top - bottom < 18)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa3, 0x82, 0x60, 0x01, 0x51, 0x94, 0x50, 0x82, 0x60, 0x01, 0x51, 0x93, 0x50, 0x50, 0x50, 0x50, 0x98, 0x50, 0x98, 0x96, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 - t1;
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            aot::log3<traits>(ctx, gas, t1, t2, s1, s2, s3);
            gas = ctx->gas_remaining;
            uint256_t const &s6 = top[-6];
            uint256_t const t3 = uint256_t{0x20ull} + s6;
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const t5 = uint256_t{0x40ull} + s6;
            uint256_t const t6 = aot::mload<traits>(ctx, gas, t5);
            uint256_t const &s17 = top[-17];
            uint64_t const jt = aot::jump_offset(s17);
            top[-17] = t4;
            top[-16] = t6;
            top += -16;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1867(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x51, 0x81, 0x01, 0x7f, 0x01, 0x51, 0x60, 0x80, 0x51, 0x80, 0x82, 0x01, 0x90, 0x91, 0x52, 0x60, 0x81, 0x52, 0x7f, 0x60, 0x90, 0x91, 0x01, 0x52, 0x5f, 0x90, 0x7f, 0x81, 0x14, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x51, 0x81, 0x01, 0x7f, 0x01, 0x51, 0x60, 0x80, 0x51, 0x80, 0x82, 0x01, 0x90, 0x91, 0x52, 0x60, 0x81, 0x52, 0x7f, 0x60, 0x90, 0x91, 0x01, 0x52, 0x5f, 0x90, 0x7f, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = s0 + t1;
            uint256_t const t3 = uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t2;
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const t5 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t6 = uint256_t{0x40ull} + t5;
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t6);
            aot::mstore<traits>(ctx, gas, t5, uint256_t{0xeull});
            uint256_t const t7 = t5 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t7, uint256_t{0x0ull, 0x0ull, 0x4e53464552530000ull, 0x534b49505f545241ull});
            uint256_t const t8 = aot::from_bool(t4 == uint256_t{0x623eb8022af73ba3ull, 0xf757e867d80fed46ull, 0x393d3a30de35560full, 0x520f8ead5ba46586ull});
            bool const j32 = aot::nonzero(t8);
            top[1] = uint256_t{0x0ull};
            top[2] = t4;
            top += 2;
            if (j32) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x18f5); }
            MONAD_AOT_TAIL return b_18ed<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18ed(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x91, 0x50, 0x50, 0x61, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x91, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-1] = uint256_t{0x0ull};
            top += -1;
            MONAD_AOT_TAIL return b_1a7c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18fe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x86, 0x15}, 8, 0));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x86, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s7));
            top[0] = t1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1901);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1907(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x85, 0x15}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x85, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s6));
            top[0] = t1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x190a);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1910(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x85, 0x87, 0x13}, 8, 1));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x85, 0x87, 0x13}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::from_bool(slt(s6, s7));
            top[0] = t1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1914);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_191a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b08ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_195d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x84, 0x73, 0x16, 0x81, 0x73, 0x16, 0x14, 0x80, 0x15, 0x61, 0x57}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x84, 0x73, 0x16, 0x81, 0x73, 0x16, 0x14, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s4;
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s0;
            uint256_t const t3 = aot::from_bool(t2 == t1);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j10 = aot::nonzero(t4);
            top[1] = t3;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x19ac); }
            MONAD_AOT_TAIL return b_1992<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1992(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x73, 0x81, 0x16, 0x33, 0x14}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x73, 0x81, 0x16, 0x33, 0x14}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t3 = aot::from_bool(t2 == t1);
            top[0] = t3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x19ac);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_19b1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b08ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a21(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x73, 0x81, 0x16, 0x33, 0x14}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x73, 0x81, 0x16, 0x33, 0x14}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t3 = aot::from_bool(t2 == t1);
            top[0] = t3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a3b);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a40(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b08ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1a7c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x95, 0x94, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x95, 0x94, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint64_t const jt = aot::jump_offset(s6);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-6] = m0;
            top += -6;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1a85(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x51, 0x81, 0x01, 0x7f, 0x01, 0x51, 0x60, 0x80, 0x51, 0x80, 0x82, 0x01, 0x90, 0x91, 0x52, 0x60, 0x81, 0x52, 0x7f, 0x60, 0x90, 0x91, 0x01, 0x52, 0x5f, 0x90, 0x81, 0x90, 0x7f, 0x81, 0x14, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x51, 0x81, 0x01, 0x7f, 0x01, 0x51, 0x60, 0x80, 0x51, 0x80, 0x82, 0x01, 0x90, 0x91, 0x52, 0x60, 0x81, 0x52, 0x7f, 0x60, 0x90, 0x91, 0x01, 0x52, 0x5f, 0x90, 0x81, 0x90, 0x7f, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = s0 + t1;
            uint256_t const t3 = uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t2;
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const t5 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t6 = uint256_t{0x40ull} + t5;
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t6);
            aot::mstore<traits>(ctx, gas, t5, uint256_t{0xdull});
            uint256_t const t7 = t5 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t7, uint256_t{0x0ull, 0x0ull, 0x5346455253000000ull, 0x4e45545f5452414eull});
            uint256_t const t8 = aot::from_bool(t4 == uint256_t{0x8c48ef9abe2a7eabull, 0x6579c006b3b26b87ull, 0xb50895d7ef6c8661ull, 0x1c3af6d2a9b692a8ull});
            bool const j34 = aot::nonzero(t8);
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top[3] = t4;
            top += 3;
            if (j34) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b18); }
            MONAD_AOT_TAIL return b_1b0d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b0d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0x92, 0x50, 0x92, 0x50, 0x50, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0x92, 0x50, 0x92, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-2] = uint256_t{0x0ull};
            top[-1] = uint256_t{0x0ull};
            top += -1;
            MONAD_AOT_TAIL return b_1cd2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b20(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b2e);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b36(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b3d);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b51(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x86, 0x15}, 8, 0));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x86, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s7));
            top[0] = t1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b54);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b5a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x5f, 0x87, 0x89, 0x18, 0x12}, 9, 2));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x5f, 0x87, 0x89, 0x18, 0x12}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = s8 ^ s7;
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x0ull}));
            top[0] = t2;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b60);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b66(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b0aull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ba9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x86, 0x73, 0x16, 0x81, 0x73, 0x16, 0x14, 0x15, 0x80, 0x61, 0x57}, 7, 3));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x86, 0x73, 0x16, 0x81, 0x73, 0x16, 0x14, 0x15, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s6;
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s0;
            uint256_t const t3 = aot::from_bool(t2 == t1);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j10 = aot::nonzero(t4);
            top[1] = t4;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1bf8); }
            MONAD_AOT_TAIL return b_1bde<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1bde(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x73, 0x86, 0x16, 0x15, 0x15}, 7, 1));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x73, 0x86, 0x16, 0x15, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s6 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[0] = t3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1bf8);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1bfe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b0aull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c41(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x85, 0x73, 0x16, 0x81, 0x73, 0x16, 0x14, 0x15, 0x80, 0x61, 0x57}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x85, 0x73, 0x16, 0x81, 0x73, 0x16, 0x14, 0x15, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s5;
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s0;
            uint256_t const t3 = aot::from_bool(t2 == t1);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j10 = aot::nonzero(t4);
            top[1] = t4;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1c90); }
            MONAD_AOT_TAIL return b_1c76<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c76(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x73, 0x87, 0x16, 0x15, 0x15}, 8, 1));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x73, 0x87, 0x16, 0x15, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = s7 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            top[0] = t3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1c90);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c96(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b0aull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1cd2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x95, 0x50, 0x95, 0x93, 0x50, 0x50, 0x50, 0x50, 0x56}, 8, 0));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x95, 0x50, 0x95, 0x93, 0x50, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint64_t const jt = aot::jump_offset(s7);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-7] = m1;
            top[-6] = m0;
            top += -6;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1cdc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x01, 0x51, 0x5f, 0x90, 0x80, 0x84, 0x81, 0x10, 0x80, 0x61, 0x57}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x01, 0x51, 0x5f, 0x90, 0x80, 0x84, 0x81, 0x10, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x20ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::from_bool(t2 < s1);
            bool const j13 = aot::nonzero(t3);
            top[1] = uint256_t{0x0ull};
            top[2] = t2;
            top[3] = t2;
            top[4] = t3;
            top += 4;
            if (j13) { MONAD_AOT_TAIL return b_1d12<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1ced<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ced(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x61, 0x61, 0x60, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x61, 0x61, 0x60, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[0] = uint256_t{0x2710ull};
            top[1] = uint256_t{0x1cfbull};
            top[2] = uint256_t{0x64ull};
            top[3] = uint256_t{0x2710ull};
            top += 3;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1cfb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x90, 0x87, 0x61, 0x56}, 7, 3));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x90, 0x87, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[0] = uint256_t{0x1d05ull};
            top[1] = m0;
            top[2] = m6;
            top += 2;
            MONAD_AOT_TAIL return b_3751<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1d05(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x1d0full};
            top[0] = m1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_3768<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1d0f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x11}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x11}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(s0 < s1);
            top[0] = t1;
            MONAD_AOT_TAIL return b_1d12<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1d12(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_1deb<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1d18<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d18(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0x51, 0x80, 0x82, 0x01, 0x90, 0x91, 0x52, 0x60, 0x81, 0x52, 0x7f, 0x60, 0x90, 0x91, 0x01, 0x52, 0x7f, 0x82, 0x01, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0x51, 0x80, 0x82, 0x01, 0x90, 0x91, 0x52, 0x60, 0x81, 0x52, 0x7f, 0x60, 0x90, 0x91, 0x01, 0x52, 0x7f, 0x82, 0x01, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = uint256_t{0x40ull} + t1;
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t2);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x5ull});
            uint256_t const t3 = t1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x4445585632000000ull});
            uint256_t const &s1 = top[-1];
            uint256_t const t4 = s1 + uint256_t{0xa0c7b6da00f5b24aull, 0x3a5ebff09360b90cull, 0x24779d52750d68d3ull, 0x2ee71ed3ac8c9a55ull};
            bool const j22 = aot::nonzero(t4);
            if (j22) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1de6); }
            MONAD_AOT_TAIL return b_1d74<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d74(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x60, 0x83, 0x01, 0x51, 0x84, 0x81, 0x10, 0x80, 0x61, 0x57}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x60, 0x83, 0x01, 0x51, 0x84, 0x81, 0x10, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x60ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s4 = top[-4];
            uint256_t const t3 = aot::from_bool(t2 < s4);
            bool const j10 = aot::nonzero(t3);
            top[0] = t2;
            top[1] = t3;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1da7); }
            MONAD_AOT_TAIL return b_1d82<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d82(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x61, 0x61, 0x60, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x61, 0x61, 0x60, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[0] = uint256_t{0x2710ull};
            top[1] = uint256_t{0x1d90ull};
            top[2] = uint256_t{0x64ull};
            top[3] = uint256_t{0x2710ull};
            top += 3;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1dad(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b01ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1deb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x94, 0x50}, 5, 1));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x94, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-4] = m0;
            MONAD_AOT_TAIL return b_1def<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1def(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x92, 0x50, 0x50, 0x50}, 5, 1));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x92, 0x50, 0x50, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-2] = m4;
            top += -2;
            MONAD_AOT_TAIL return b_1df5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1df5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x91, 0x50, 0x50, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x91, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-3] = m0;
            top += -3;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1dfb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x73, 0x83, 0x16, 0x01, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x73, 0x83, 0x16, 0x01, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = t1 + uint256_t{0x364fa4bc1ca64812ull, 0x7a7df0848d2f6d90ull, 0xffffffff32a01dc3ull, 0xffffffffffffffffull};
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return b_1f83<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1e39<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1e39(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x73, 0x60, 0x82, 0x01, 0x52, 0x5f, 0x90, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x86, 0x5a, 0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}, 0, 10));
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x73, 0x60, 0x82, 0x01, 0x52, 0x5f, 0x90, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x86, 0x5a, 0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdd62ed3e00000000ull});
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t3 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = t1 + uint256_t{0x24ull};
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x2c186f3611aeafa6ull, 0x75cebf0eb9ed34aeull, 0xf047ab4cull, 0x0ull});
            uint256_t const t5 = uint256_t{0x44ull} + t1;
            uint256_t const t6 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t7 = t5 - t6;
            uint256_t const t8 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k32_1 = uint256_t{0xc9b05b43e359b7eeull, 0x85820f7b72d0926full, 0xcd5fe23cull, 0x0ull};
            uint256_t const k32_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r32;
            runtime::staticcall<traits>(ctx, &r32, &t8, &k32_1, &t6, &t7, &t6, &k32_5, (aot::gas_of<traits>({0x15, 0x80, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(r32));
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            bool const j37 = aot::nonzero(t10);
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0xc9b05b43e359b7eeull, 0x85820f7b72d0926full, 0xcd5fe23cull, 0x0ull};
            top[3] = uint256_t{0xdd62ed3eull};
            top[4] = t5;
            top[5] = t9;
            top += 5;
            if (j37) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1eba); }
            MONAD_AOT_TAIL return b_1eb3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1eb3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const k3_0 = uint256_t{0x0ull};
            uint256_t const k3_1 = uint256_t{0x0ull};
            ctx->gas_remaining = gas;
            runtime::returndatacopy<traits>(ctx, &k3_0, &k3_1, &t1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, t2);
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ee5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x73, 0x60, 0x82, 0x01, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x82, 0x90, 0x52, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x73, 0x60, 0x82, 0x01, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x82, 0x90, 0x52, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xb3db428b00000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0xc9b05b43e359b7eeull, 0x85820f7b72d0926full, 0xcd5fe23cull, 0x0ull});
            uint256_t const t3 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t4 = t1 + uint256_t{0x24ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const t5 = t1 + uint256_t{0x44ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t5, s0);
            uint256_t const t6 = uint256_t{0x64ull} + t1;
            top[1] = uint256_t{0x2c186f3611aeafa6ull, 0x75cebf0eb9ed34aeull, 0xf047ab4cull, 0x0ull};
            top[2] = uint256_t{0xb3db428bull};
            top[3] = t6;
            top += 3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1f51);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f65(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1f73(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const k3_0 = uint256_t{0x0ull};
            uint256_t const k3_1 = uint256_t{0x0ull};
            ctx->gas_remaining = gas;
            runtime::returndatacopy<traits>(ctx, &k3_0, &k3_1, &t1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, t2);
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1f7f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top += -3;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1f83(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x73, 0x83, 0x16, 0x01, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x73, 0x83, 0x16, 0x01, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = t1 + uint256_t{0x3f32e12d2a6f6278ull, 0xe59806cc0d194cc0ull, 0xffffffff6e83117full, 0xffffffffffffffffull};
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return b_1f7f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1fc1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fc1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x73, 0x60, 0x82, 0x01, 0x52, 0x5f, 0x90, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x86, 0x5a, 0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}, 0, 10));
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x73, 0x60, 0x82, 0x01, 0x52, 0x5f, 0x90, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x86, 0x5a, 0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdd62ed3e00000000ull});
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t3 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = t1 + uint256_t{0x24ull};
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x2c186f3611aeafa6ull, 0x75cebf0eb9ed34aeull, 0xf047ab4cull, 0x0ull});
            uint256_t const t5 = uint256_t{0x44ull} + t1;
            uint256_t const t6 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t7 = t5 - t6;
            uint256_t const t8 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k32_1 = uint256_t{0xc0cd1ed2d5909d88ull, 0x1a67f933f2e6b33full, 0x917cee80ull, 0x0ull};
            uint256_t const k32_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r32;
            runtime::staticcall<traits>(ctx, &r32, &t8, &k32_1, &t6, &t7, &t6, &k32_5, (aot::gas_of<traits>({0x15, 0x80, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(r32));
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            bool const j37 = aot::nonzero(t10);
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0xc0cd1ed2d5909d88ull, 0x1a67f933f2e6b33full, 0x917cee80ull, 0x0ull};
            top[3] = uint256_t{0xdd62ed3eull};
            top[4] = t5;
            top[5] = t9;
            top += 5;
            if (j37) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2042); }
            MONAD_AOT_TAIL return b_203b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_203b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const k3_0 = uint256_t{0x0ull};
            uint256_t const k3_1 = uint256_t{0x0ull};
            ctx->gas_remaining = gas;
            runtime::returndatacopy<traits>(ctx, &k3_0, &k3_1, &t1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, t2);
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_206d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x73, 0x60, 0x82, 0x01, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x82, 0x90, 0x52, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x5f, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x5f, 0x87, 0x80, 0x3b, 0x15, 0x80, 0x15, 0x61, 0x57}, 1, 12));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1012)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x73, 0x60, 0x82, 0x01, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x82, 0x90, 0x52, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x5f, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x5f, 0x87, 0x80, 0x3b, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xb3db428b00000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0xc0cd1ed2d5909d88ull, 0x1a67f933f2e6b33full, 0x917cee80ull, 0x0ull});
            uint256_t const t3 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t4 = t1 + uint256_t{0x24ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const t5 = t1 + uint256_t{0x44ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t5, s0);
            uint256_t const t6 = uint256_t{0x64ull} + t1;
            uint256_t const t7 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t8 = t6 - t7;
            uint256_t const k37_0 = uint256_t{0x2c186f3611aeafa6ull, 0x75cebf0eb9ed34aeull, 0xf047ab4cull, 0x0ull};
            ctx->gas_remaining = gas;
            uint256_t r37;
            runtime::extcodesize<traits>(ctx, &r37, &k37_0);
            gas = ctx->gas_remaining;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(r37));
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            bool const j42 = aot::nonzero(t10);
            top[1] = uint256_t{0x2c186f3611aeafa6ull, 0x75cebf0eb9ed34aeull, 0xf047ab4cull, 0x0ull};
            top[2] = uint256_t{0xb3db428bull};
            top[3] = t6;
            top[4] = uint256_t{0x0ull};
            top[5] = t7;
            top[6] = t8;
            top[7] = t7;
            top[8] = uint256_t{0x0ull};
            top[9] = uint256_t{0x2c186f3611aeafa6ull, 0x75cebf0eb9ed34aeull, 0xf047ab4cull, 0x0ull};
            top[10] = t9;
            top += 10;
            if (j42) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1f68); }
            MONAD_AOT_TAIL return b_20ec<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_20ec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_20ef(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x60, 0x82, 0x90, 0x1c, 0x81, 0x16, 0x90, 0x60, 0x83, 0x90, 0x1c, 0x16, 0x81, 0x15, 0x80, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x60, 0x82, 0x90, 0x1c, 0x81, 0x16, 0x90, 0x60, 0x83, 0x90, 0x1c, 0x16, 0x81, 0x15, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shr_c<91>(s0);
            uint256_t const t2 = uint256_t{0xffffffffffffffffull} & t1;
            uint256_t const t3 = aot::shr_c<155>(s0);
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffffull};
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t2));
            bool const j18 = aot::nonzero(t5);
            top[1] = t2;
            top[2] = t4;
            top[3] = t5;
            top += 3;
            if (j18) { MONAD_AOT_TAIL return b_2111<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_210e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_210e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x80, 0x15}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x80, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s1));
            top[0] = t1;
            MONAD_AOT_TAIL return b_2111<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2111(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_214d<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2117<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2117(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x62, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x62, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xd50d751200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x11171ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_214d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x83, 0x16, 0x60, 0x84, 0x90, 0x1c, 0x64, 0x16, 0x42, 0x81, 0x81, 0x03, 0x91, 0x60, 0x87, 0x90, 0x1c, 0x61, 0x16, 0x91, 0x14, 0x80, 0x61, 0x57}, 3, 6));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x83, 0x16, 0x60, 0x84, 0x90, 0x1c, 0x64, 0x16, 0x42, 0x81, 0x81, 0x03, 0x91, 0x60, 0x87, 0x90, 0x1c, 0x61, 0x16, 0x91, 0x14, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 & uint256_t{0xffffull};
            uint256_t const t2 = aot::shr_c<58>(s2);
            uint256_t const t3 = uint256_t{0x1ffffffffull} & t2;
            uint256_t const t4 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const t5 = t4 - t3;
            uint256_t const t6 = aot::shr_c<234>(s2);
            uint256_t const t7 = uint256_t{0x7fffull} & t6;
            uint256_t const t8 = aot::from_bool(t4 == t3);
            bool const j25 = aot::nonzero(t8);
            top[1] = t1;
            top[2] = t5;
            top[3] = t7;
            top[4] = t8;
            top += 4;
            if (j25) { MONAD_AOT_TAIL return b_2177<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2174<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2174(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x82, 0x15}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x82, 0x15}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s3));
            top[0] = t1;
            MONAD_AOT_TAIL return b_2177<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2177(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j3 = aot::nonzero(s0);
            if (j3) { MONAD_AOT_TAIL return b_2182<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_217d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_217d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x80, 0x60, 0x14}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x80, 0x60, 0x14}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(uint256_t{0x1ull} == s1);
            top[0] = t1;
            MONAD_AOT_TAIL return b_2182<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2182(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_218f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2188<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2188(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x91, 0x50, 0x91, 0x56}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x91, 0x50, 0x91, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint64_t const jt = aot::jump_offset(s6);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-6] = m4;
            top[-5] = m3;
            top += -5;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_218f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x64, 0x84, 0x84, 0x02, 0x83, 0x02, 0x04, 0x84, 0x01, 0x93, 0x50, 0x61, 0x60, 0x87, 0x90, 0x1c, 0x16, 0x92, 0x50, 0x82, 0x60, 0x03, 0x61, 0x57}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x64, 0x84, 0x84, 0x02, 0x83, 0x02, 0x04, 0x84, 0x01, 0x93, 0x50, 0x61, 0x60, 0x87, 0x90, 0x1c, 0x16, 0x92, 0x50, 0x82, 0x60, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::mul(s2, s3);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::mul(s1, t1);
            uint256_t const t3 = aot::udiv(t2, uint256_t{0x496cebb800ull});
            uint256_t const t4 = s3 + t3;
            uint256_t const &s5 = top[-5];
            uint256_t const t5 = aot::shr_c<219>(s5);
            uint256_t const t6 = t5 & uint256_t{0x7fffull};
            uint256_t const t7 = uint256_t{0x1ull} - t6;
            bool const j24 = aot::nonzero(t7);
            top[-3] = t4;
            top[-2] = t6;
            if (j24) { MONAD_AOT_TAIL return b_21ba<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_21b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21b3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x91, 0x50, 0x91, 0x56}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x91, 0x50, 0x91, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint64_t const jt = aot::jump_offset(s6);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-6] = m4;
            top[-5] = m3;
            top += -5;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_21ba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x60, 0x16, 0x60, 0x03, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x60, 0x16, 0x60, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0x1ull} & s2;
            uint256_t const t2 = uint256_t{0x1ull} - t1;
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return b_220f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_21c6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21c6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x92, 0x90, 0x92, 0x1c, 0x91, 0x82, 0x6c, 0x81, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x92, 0x90, 0x92, 0x1c, 0x91, 0x82, 0x6c, 0x81, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::shr_c<1>(s2);
            bool const j10 = aot::nonzero(t1);
            top[-2] = t1;
            top[1] = t1;
            top[2] = uint256_t{0xc0914b2680000000ull, 0x7e37be2022ull, 0x0ull, 0x0ull};
            top += 2;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x21e8); }
            MONAD_AOT_TAIL return b_21e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_21e1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x21e8ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x368a);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_220f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x92, 0x90, 0x92, 0x1c, 0x91, 0x63, 0x60, 0x87, 0x90, 0x1c, 0x61, 0x16, 0x61, 0x85, 0x01, 0x02, 0x6b, 0x02, 0x04, 0x92, 0x50}, 6, 4));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x92, 0x90, 0x92, 0x1c, 0x91, 0x63, 0x60, 0x87, 0x90, 0x1c, 0x61, 0x16, 0x61, 0x85, 0x01, 0x02, 0x6b, 0x02, 0x04, 0x92, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::shr_c<1>(s2);
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = aot::shr_c<30>(s5);
            uint256_t const t3 = uint256_t{0x3fffull} & t2;
            uint256_t const t4 = t1 + uint256_t{0x2710ull};
            uint256_t const t5 = aot::mul(t4, t3);
            uint256_t const t6 = aot::mul(uint256_t{0x9fd0803ce8000000ull, 0x33b2e3cull, 0x0ull, 0x0ull}, t5);
            uint256_t const t7 = aot::udiv(t6, uint256_t{0x5f5e100ull});
            top[-2] = t7;
            MONAD_AOT_TAIL return b_223c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_223c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x60, 0x16, 0x60, 0x03, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x60, 0x16, 0x60, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x1ull} & s0;
            uint256_t const t2 = uint256_t{0x1ull} - t1;
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return b_2273<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2248<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2248(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x1c, 0x61, 0x81, 0x01, 0x6b, 0x82, 0x02, 0x81, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x1c, 0x61, 0x81, 0x01, 0x6b, 0x82, 0x02, 0x81, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shr_c<1>(s0);
            uint256_t const t2 = t1 + uint256_t{0x2710ull};
            uint256_t const t3 = aot::mul(t1, uint256_t{0x9fd0803ce8000000ull, 0x33b2e3cull, 0x0ull, 0x0ull});
            bool const j10 = aot::nonzero(t2);
            top[0] = t1;
            top[1] = t2;
            top[2] = t3;
            top += 2;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x226b); }
            MONAD_AOT_TAIL return b_2264<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2264(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x226bull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x368a);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2273(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x1c, 0x61, 0x81, 0x01, 0x6b, 0x82, 0x02, 0x81, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x1c, 0x61, 0x81, 0x01, 0x6b, 0x82, 0x02, 0x81, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shr_c<1>(s0);
            uint256_t const t2 = t1 + uint256_t{0x2710ull};
            uint256_t const t3 = aot::mul(t1, uint256_t{0x9fd0803ce8000000ull, 0x33b2e3cull, 0x0ull, 0x0ull});
            bool const j11 = aot::nonzero(t2);
            top[0] = t1;
            top[1] = t2;
            top[2] = t3;
            top += 2;
            if (j11) { MONAD_AOT_TAIL return b_2297<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2290<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2290(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x2297ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x368a);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2297(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x04, 0x6b, 0x03, 0x90, 0x50}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x04, 0x6b, 0x03, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::udiv(s0, s1);
            uint256_t const t2 = uint256_t{0x9fd0803ce8000000ull, 0x33b2e3cull, 0x0ull, 0x0ull} - t1;
            top[-2] = t2;
            top += -2;
            MONAD_AOT_TAIL return b_22a9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_22a9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x76, 0x83, 0x82, 0x02, 0x61, 0x02, 0x61, 0x88, 0x16, 0x91, 0x90, 0x04, 0x02, 0x60, 0x87, 0x90, 0x1c, 0x61, 0x16, 0x61, 0x03, 0x02, 0x92, 0x50, 0x68, 0x85, 0x84, 0x02, 0x83, 0x02, 0x04, 0x85, 0x01, 0x94, 0x50, 0x50, 0x50, 0x50, 0x91, 0x50, 0x91, 0x56}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x76, 0x83, 0x82, 0x02, 0x61, 0x02, 0x61, 0x88, 0x16, 0x91, 0x90, 0x04, 0x02, 0x60, 0x87, 0x90, 0x1c, 0x61, 0x16, 0x61, 0x03, 0x02, 0x92, 0x50, 0x68, 0x85, 0x84, 0x02, 0x83, 0x02, 0x04, 0x85, 0x01, 0x94, 0x50, 0x50, 0x50, 0x50, 0x91, 0x50, 0x91, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mul(s0, s2);
            uint256_t const t2 = aot::mul(uint256_t{0x2710ull}, t1);
            uint256_t const &s5 = top[-5];
            uint256_t const t3 = s5 & uint256_t{0xffffull};
            uint256_t const t4 = aot::udiv(t2, uint256_t{0x9240000000000000ull, 0xc51999090b65f67dull, 0xa70c3c40a64e6ull, 0x0ull});
            uint256_t const t5 = aot::mul(t4, t3);
            uint256_t const t6 = aot::shr_c<16>(s5);
            uint256_t const t7 = uint256_t{0x3fffull} & t6;
            uint256_t const t8 = uint256_t{0x2710ull} - t7;
            uint256_t const t9 = aot::mul(t8, t5);
            uint256_t const &s4 = top[-4];
            uint256_t const t10 = aot::mul(t9, s4);
            uint256_t const &s1 = top[-1];
            uint256_t const t11 = aot::mul(s1, t10);
            uint256_t const t12 = aot::udiv(t11, uint256_t{0xb5a660ea44b80000ull, 0x1ull, 0x0ull, 0x0ull});
            uint256_t const t13 = s4 + t12;
            uint256_t const &s6 = top[-6];
            uint64_t const jt = aot::jump_offset(s6);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-6] = t13;
            top[-5] = m3;
            top += -5;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_22fd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x80, 0x80, 0x60, 0x81, 0x73, 0x89, 0x16, 0x15, 0x61, 0x57}, 4, 7));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x80, 0x80, 0x60, 0x81, 0x73, 0x89, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j11 = aot::nonzero(t2);
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top[3] = uint256_t{0x0ull};
            top[4] = uint256_t{0x8ull};
            top[5] = uint256_t{0x0ull};
            top += 5;
            if (j11) { MONAD_AOT_TAIL return b_2325<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2320<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2320(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x88, 0x61, 0x56}, 9, 2));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x88, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[1] = m8;
            top += 1;
            MONAD_AOT_TAIL return b_2327<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2325(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x33}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x33}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_2327<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2327(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x90, 0x81, 0x16, 0x82, 0x52, 0x60, 0x80, 0x83, 0x01, 0x93, 0x90, 0x93, 0x52, 0x60, 0x91, 0x82, 0x01, 0x5f, 0x90, 0x81, 0x20, 0x91, 0x8a, 0x16, 0x81, 0x52, 0x92, 0x52, 0x81, 0x20, 0x54, 0x91, 0x50, 0x81, 0x90, 0x03, 0x61, 0x57}, 9, 3));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x90, 0x81, 0x16, 0x82, 0x52, 0x60, 0x80, 0x83, 0x01, 0x93, 0x90, 0x93, 0x52, 0x60, 0x91, 0x82, 0x01, 0x5f, 0x90, 0x81, 0x20, 0x91, 0x8a, 0x16, 0x81, 0x52, 0x92, 0x52, 0x81, 0x20, 0x54, 0x91, 0x50, 0x81, 0x90, 0x03, 0x61, 0x57}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s0;
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, t1);
            uint256_t const t2 = s1 + uint256_t{0x20ull};
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t2, s2);
            uint256_t const t3 = uint256_t{0x40ull} + s1;
            auto const h22 = aot::sha3_any<traits>(ctx, gas, uint256_t{0x0ull}, t3);
            gas = ctx->gas_remaining;
            uint256_t const &s8 = top[-8];
            uint256_t const t4 = s8 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t4);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, h22);
            uint256_t const t5 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t6 = aot::sload<traits>(ctx, gas, t5);
            uint256_t const t7 = uint256_t{0x0ull} - t6;
            bool const j39 = aot::nonzero(t7);
            top[-3] = t6;
            top += -3;
            if (j39) { MONAD_AOT_TAIL return b_239c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2367<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2367(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2af9ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_239c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x87, 0x16, 0x15, 0x80, 0x15, 0x61, 0x57}, 7, 3));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x87, 0x16, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s6 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j8 = aot::nonzero(t3);
            top[1] = t2;
            top += 1;
            if (j8) { MONAD_AOT_TAIL return b_23c4<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_23bb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_23bb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x60, 0x60, 0x82, 0x90, 0x1c, 0x14}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x60, 0x60, 0x82, 0x90, 0x1c, 0x14}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<255>(s1);
            uint256_t const t2 = aot::from_bool(t1 == uint256_t{0x1ull});
            top[0] = t2;
            MONAD_AOT_TAIL return b_23c4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_23c4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_23ff<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_23ca<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_23ca(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2afaull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_23ff(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x87, 0x16, 0x61, 0x57}, 7, 2));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x87, 0x16, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s6 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_241e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_241b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_241b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x33, 0x96, 0x50}, 7, 1));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x33, 0x96, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            top[-6] = t1;
            MONAD_AOT_TAIL return b_241e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_241e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x66, 0x60, 0x82, 0x90, 0x1c, 0x16, 0x60, 0x60, 0x83, 0x90, 0x1c, 0x81, 0x16, 0x91, 0x90, 0x91, 0x1b, 0x90, 0x62, 0x60, 0x84, 0x90, 0x1c, 0x16, 0x60, 0x84, 0x90, 0x1c, 0x90, 0x91, 0x16, 0x1b, 0x60, 0x83, 0x90, 0x1c, 0x61, 0x16, 0x81, 0x15, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x66, 0x60, 0x82, 0x90, 0x1c, 0x16, 0x60, 0x60, 0x83, 0x90, 0x1c, 0x81, 0x16, 0x91, 0x90, 0x91, 0x1b, 0x90, 0x62, 0x60, 0x84, 0x90, 0x1c, 0x16, 0x60, 0x84, 0x90, 0x1c, 0x90, 0x91, 0x16, 0x1b, 0x60, 0x83, 0x90, 0x1c, 0x61, 0x16, 0x81, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shr_c<9>(s0);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffull};
            uint256_t const t3 = aot::shr_c<1>(s0);
            uint256_t const t4 = uint256_t{0xffull} & t3;
            uint256_t const t5 = aot::shl(t4, t2);
            uint256_t const t6 = aot::shr_c<226>(s0);
            uint256_t const t7 = t6 & uint256_t{0x3ffffull};
            uint256_t const t8 = aot::shr_c<218>(s0);
            uint256_t const t9 = uint256_t{0xffull} & t8;
            uint256_t const t10 = aot::shl(t9, t7);
            uint256_t const t11 = aot::shr_c<244>(s0);
            uint256_t const t12 = uint256_t{0x3ffull} & t11;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t10));
            bool const j42 = aot::nonzero(t13);
            top[1] = t5;
            top[2] = t10;
            top[3] = t12;
            top += 3;
            if (j42) { MONAD_AOT_TAIL return b_24aa<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_245d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_245d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x60, 0x60, 0x60, 0x87, 0x90, 0x1c, 0x64, 0x16, 0x02, 0x04, 0x60, 0x60, 0x42, 0x02, 0x04, 0x03, 0x90, 0x50, 0x81, 0x81, 0x10, 0x15, 0x61, 0x57}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x60, 0x60, 0x60, 0x87, 0x90, 0x1c, 0x64, 0x16, 0x02, 0x04, 0x60, 0x60, 0x42, 0x02, 0x04, 0x03, 0x90, 0x50, 0x81, 0x81, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::shr_c<129>(s3);
            uint256_t const t2 = uint256_t{0x1ffffffffull} & t1;
            uint256_t const t3 = aot::mul(t2, uint256_t{0xaull});
            uint256_t const t4 = aot::udiv(t3, uint256_t{0x24ull});
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const t6 = aot::mul(t5, uint256_t{0xaull});
            uint256_t const t7 = aot::udiv(t6, uint256_t{0x24ull});
            uint256_t const t8 = t7 - t4;
            uint256_t const &s0 = top[0];
            uint256_t const t9 = aot::from_bool(t8 < s0);
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            bool const j24 = aot::nonzero(t10);
            top[1] = t8;
            top += 1;
            if (j24) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x24a1); }
            MONAD_AOT_TAIL return b_2482<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2482(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x81, 0x84, 0x02, 0x81, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x81, 0x84, 0x02, 0x81, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(s2, s0);
            uint256_t const &s1 = top[-1];
            bool const j6 = aot::nonzero(s1);
            uint256_t const m1 = s1;
            top[1] = m1;
            top[2] = t1;
            top += 2;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2492); }
            MONAD_AOT_TAIL return b_248b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_248b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x2492ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x368a);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24aa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x61, 0x85, 0x85, 0x61, 0x56}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x61, 0x85, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x24b5ull};
            top[3] = m3;
            top[4] = m2;
            top += 4;
            MONAD_AOT_TAIL return b_30f2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24b5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x84, 0x60, 0x16, 0x60, 0x03, 0x61, 0x57}, 6, 1));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x84, 0x60, 0x16, 0x60, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = uint256_t{0x1ull} & s5;
            uint256_t const t2 = uint256_t{0x1ull} - t1;
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x252d); }
            MONAD_AOT_TAIL return b_24c3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_24c3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x89, 0x13, 0x15, 0x61, 0x57}, 9, 2));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x89, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s8));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j5 = aot::nonzero(t2);
            if (j5) { MONAD_AOT_TAIL return b_24f7<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_24cb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_24cb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x87, 0x61, 0x64, 0x8b, 0x61, 0x56}, 9, 5));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x87, 0x61, 0x64, 0x8b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[1] = m7;
            top[2] = uint256_t{0x24daull};
            top[3] = uint256_t{0xe8d4a51000ull};
            top[4] = m8;
            top += 4;
            MONAD_AOT_TAIL return b_377b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24da(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x24e4ull};
            top[0] = m1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_37c6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24e4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x96, 0x50, 0x61, 0x87, 0x85, 0x61, 0x56}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x96, 0x50, 0x61, 0x87, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-7] = m0;
            top[0] = uint256_t{0x24f0ull};
            top[1] = m0;
            top[2] = m4;
            top += 2;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24f0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x93, 0x50, 0x61, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x93, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-4] = m0;
            top += -1;
            MONAD_AOT_TAIL return b_2558<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24f7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x8a, 0x61, 0x56}, 9, 4));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[1] = uint256_t{0x250full};
            top[2] = uint256_t{0x2503ull};
            top[3] = m8;
            top += 3;
            MONAD_AOT_TAIL return b_3641<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2503(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x64, 0x8a, 0x61, 0x56}, 10, 3));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x64, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[1] = uint256_t{0xe8d4a51000ull};
            top[2] = m9;
            top += 2;
            MONAD_AOT_TAIL return b_3183<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_250f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x90, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x2518ull};
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_3641<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2518(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x96, 0x50, 0x61, 0x87, 0x61, 0x56}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x96, 0x50, 0x61, 0x87, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-7] = m0;
            top[0] = uint256_t{0x2523ull};
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_3641<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2523(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x90, 0x85, 0x61, 0x56}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x90, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[0] = uint256_t{0x24f0ull};
            top[1] = m0;
            top[2] = m4;
            top += 2;
            MONAD_AOT_TAIL return b_373e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2539(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x86, 0x85, 0x61, 0x56}, 6, 4));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x86, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[1] = uint256_t{0x24f0ull};
            top[2] = m5;
            top[3] = m3;
            top += 3;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2558(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x5f, 0x8a, 0x12, 0x15, 0x61, 0x57}, 9, 3));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x5f, 0x8a, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = aot::from_bool(slt(s8, uint256_t{0x0ull}));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            top[1] = uint256_t{0x0ull};
            top += 1;
            if (j7) { MONAD_AOT_TAIL return b_25ec<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2562<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2562(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x85, 0x10, 0x15, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x85, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s4 < s1);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j5 = aot::nonzero(t2);
            if (j5) { MONAD_AOT_TAIL return b_259f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_256a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_256a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2afbull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_259f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x15, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s3));
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_25ec<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_25a6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_25a6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x87, 0x87, 0x01, 0x5f, 0x03, 0x84, 0x81, 0x11, 0x15, 0x61, 0x57}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x87, 0x87, 0x01, 0x5f, 0x03, 0x84, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = s6 + s7;
            uint256_t const t2 = uint256_t{0x0ull} - t1;
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = aot::from_bool(s3 < t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j10 = aot::nonzero(t4);
            top[1] = t2;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x25cd); }
            MONAD_AOT_TAIL return b_25b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_25b3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x84, 0x83, 0x11, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x84, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::from_bool(s4 < s2);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x25bf); }
            MONAD_AOT_TAIL return b_25ba<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_25ba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x25c3);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_25d5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x25de);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_25ec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x61, 0x87, 0x87, 0x85, 0x61, 0x56}, 6, 6));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x61, 0x87, 0x87, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x25f8ull};
            top[3] = m5;
            top[4] = m4;
            top[5] = m1;
            top += 5;
            MONAD_AOT_TAIL return b_31c5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_25f8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x80, 0x5f, 0x03, 0x61, 0x57}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x80, 0x5f, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x0ull} - s0;
            bool const j7 = aot::nonzero(t1);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2609); }
            MONAD_AOT_TAIL return b_2602<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2602(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x94, 0x50, 0x61, 0x56}, 5, 1));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x94, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-4] = uint256_t{0x0ull};
            MONAD_AOT_TAIL return b_26c8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2611(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x8b, 0x13, 0x15, 0x61, 0x57}, 11, 2));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x8b, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s10 = top[-10];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s10));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j5 = aot::nonzero(t2);
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x26a0); }
            MONAD_AOT_TAIL return b_2619<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2619(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x5f, 0x03, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x5f, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0x0ull} - s2;
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2634); }
            MONAD_AOT_TAIL return b_2620<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2620(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x60, 0x88, 0x90, 0x1c, 0x16, 0x60, 0x60, 0x89, 0x90, 0x1c, 0x16, 0x1b, 0x92, 0x50}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x60, 0x88, 0x90, 0x1c, 0x16, 0x60, 0x60, 0x89, 0x90, 0x1c, 0x16, 0x1b, 0x92, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::shr_c<208>(s6);
            uint256_t const t2 = t1 & uint256_t{0x3ffull};
            uint256_t const t3 = aot::shr_c<200>(s6);
            uint256_t const t4 = t3 & uint256_t{0xffull};
            uint256_t const t5 = aot::shl(t4, t2);
            top[-2] = t5;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2634);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_263d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x81, 0x03, 0x61, 0x81, 0x87, 0x61, 0x56}, 5, 5));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x81, 0x03, 0x61, 0x81, 0x87, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s0 - s2;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[1] = t1;
            top[2] = uint256_t{0x2649ull};
            top[3] = t1;
            top[4] = m4;
            top += 4;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_267f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x94, 0x50}, 5, 1));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x94, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-4] = uint256_t{0x50ull};
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2683);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_26a7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x83, 0x82, 0x11, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x83, 0x82, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(s2 < s0);
            bool const j5 = aot::nonzero(t1);
            top[1] = uint256_t{0x0ull};
            top += 1;
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x26b4); }
            MONAD_AOT_TAIL return b_26af<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_26af(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x26b8);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_26c8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x85, 0x10, 0x15, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x85, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::from_bool(s4 < uint256_t{0xaull});
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x26dc); }
            MONAD_AOT_TAIL return b_26d2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_26d2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x94, 0x50, 0x5f, 0x93, 0x50, 0x61, 0x56}, 5, 1));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x94, 0x50, 0x5f, 0x93, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-4] = uint256_t{0x0ull};
            top[-3] = uint256_t{0x0ull};
            MONAD_AOT_TAIL return b_270c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_26f7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x93, 0x50, 0x61, 0x56}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x93, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-3] = uint256_t{0x3e8ull};
            MONAD_AOT_TAIL return b_270c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2708(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x93, 0x50}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x93, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-3] = uint256_t{0x1ull};
            MONAD_AOT_TAIL return b_270c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_270c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x86, 0x60, 0x60, 0x5f, 0x61, 0x56}, 6, 6));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x86, 0x60, 0x60, 0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[1] = uint256_t{0x271aull};
            top[2] = m5;
            top[3] = uint256_t{0x38ull};
            top[4] = uint256_t{0x8ull};
            top[5] = uint256_t{0x0ull};
            top += 5;
            MONAD_AOT_TAIL return b_28b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_271a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x95, 0x50, 0x85, 0x67, 0x60, 0x89, 0x90, 0x1c, 0x16, 0x03, 0x61, 0x57}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x95, 0x50, 0x85, 0x67, 0x60, 0x89, 0x90, 0x1c, 0x16, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::shr_c<1>(s7);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull};
            uint256_t const &s0 = top[0];
            uint256_t const t3 = t2 - s0;
            bool const j12 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[-6] = m0;
            top += -1;
            if (j12) { MONAD_AOT_TAIL return b_2767<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2732<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2732(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2affull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2767(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x60, 0x60, 0x5f, 0x61, 0x56}, 1, 6));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x60, 0x60, 0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x2775ull};
            top[2] = m0;
            top[3] = uint256_t{0x38ull};
            top[4] = uint256_t{0x8ull};
            top[5] = uint256_t{0x0ull};
            top += 5;
            MONAD_AOT_TAIL return b_28b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2775(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x60, 0x84, 0x90, 0x1b, 0x60, 0x86, 0x90, 0x1b, 0x60, 0x42, 0x90, 0x1b, 0x60, 0x84, 0x90, 0x1b, 0x60, 0x8a, 0x90, 0x1b, 0x8b, 0x7f, 0x16, 0x17, 0x17, 0x17, 0x17, 0x17, 0x60, 0x5f, 0x8f, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x20, 0x5f, 0x8e, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x20, 0x81, 0x90, 0x55, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x94, 0x50, 0x94, 0x92, 0x50, 0x50, 0x50, 0x56}, 15, 6));
            if (MONAD_UNLIKELY(top - bottom < 15)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x60, 0x84, 0x90, 0x1b, 0x60, 0x86, 0x90, 0x1b, 0x60, 0x42, 0x90, 0x1b, 0x60, 0x84, 0x90, 0x1b, 0x60, 0x8a, 0x90, 0x1b, 0x8b, 0x7f, 0x16, 0x17, 0x17, 0x17, 0x17, 0x17, 0x60, 0x5f, 0x8f, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x20, 0x5f, 0x8e, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x5f, 0x20, 0x81, 0x90, 0x55, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x94, 0x50, 0x94, 0x92, 0x50, 0x50, 0x50, 0x56}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::shl_c<244>(s4);
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = aot::shl_c<218>(s5);
            uint256_t const t3 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const t4 = aot::shl_c<129>(t3);
            uint256_t const &s0 = top[0];
            uint256_t const t5 = aot::shl_c<65>(s0);
            uint256_t const &s6 = top[-6];
            uint256_t const t6 = aot::shl_c<1>(s6);
            uint256_t const &s7 = top[-7];
            uint256_t const t7 = uint256_t{0x1ull, 0x0ull, 0xfffffffc00000000ull, 0xc000000003ffffffull} & s7;
            uint256_t const t8 = t7 | t6;
            uint256_t const t9 = t8 | t5;
            uint256_t const t10 = t9 | t4;
            uint256_t const t11 = t10 | t2;
            uint256_t const t12 = t11 | t1;
            uint256_t const &s13 = top[-13];
            uint256_t const t13 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s13;
            uint256_t const t14 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t13;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t14);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x8ull});
            uint256_t const t15 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const &s12 = top[-12];
            uint256_t const t16 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s12;
            uint256_t const t17 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t16;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t17);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t15);
            uint256_t const t18 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            aot::sstore<traits>(ctx, gas, t18, t12, (aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x94, 0x50, 0x94, 0x92, 0x50, 0x50, 0x50, 0x56}) + 0));
            uint256_t const &s14 = top[-14];
            uint64_t const jt = aot::jump_offset(s14);
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-14] = m9;
            top[-13] = m8;
            top += -13;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2844(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j3 = aot::nonzero(s0);
            if (j3) { MONAD_AOT_TAIL return b_2852<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_284a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_284a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x82, 0x04, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x82, 0x04, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<1>(s1);
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_2858<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2852(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x61, 0x02}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x61, 0x02}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mul(uint256_t{0x2710ull}, s1);
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_2858<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2858(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x50, 0x6a, 0x83, 0x11, 0x80, 0x15, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x50, 0x6a, 0x83, 0x11, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::from_bool(uint256_t{0x0ull, 0x10000ull, 0x0ull, 0x0ull} < s3);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[0] = t1;
            if (j9) { MONAD_AOT_TAIL return b_2873<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_286f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_286f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x81, 0x83, 0x11}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x81, 0x83, 0x11}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(s2 < s3);
            top[0] = t1;
            MONAD_AOT_TAIL return b_2873<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2873(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_28ae<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2879<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2879(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2b09ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_28ae(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top += -4;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_28b3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x5f, 0x85, 0x6f, 0x81, 0x11, 0x15, 0x61, 0x57}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x5f, 0x85, 0x6f, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::from_bool(uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull} < s3);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            uint256_t const m3 = s3;
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top[3] = m3;
            top += 3;
            if (j9) { MONAD_AOT_TAIL return b_28d5<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_28cf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_28cf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x91, 0x50, 0x81, 0x1c}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x91, 0x50, 0x81, 0x1c}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shr_c<128>(s0);
            top[-1] = uint256_t{0x80ull};
            top[0] = t1;
            MONAD_AOT_TAIL return b_28d5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_28d5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x81, 0x11, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xffffffffffffffffull} < s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return b_28ed<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_28e6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_28e6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x91, 0x82, 0x01, 0x91, 0x1c}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x91, 0x82, 0x01, 0x91, 0x1c}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = uint256_t{0x40ull} + s1;
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shr_c<64>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_28ed<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_28ed(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x63, 0x81, 0x11, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x63, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xffffffffull} < s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return b_2901<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_28fa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_28fa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x91, 0x82, 0x01, 0x91, 0x1c}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x91, 0x82, 0x01, 0x91, 0x1c}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = uint256_t{0x20ull} + s1;
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shr_c<32>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_2901<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2901(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x11, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xffffull} < s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return b_2913<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_290c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_290c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x91, 0x82, 0x01, 0x91, 0x1c}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x91, 0x82, 0x01, 0x91, 0x1c}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = uint256_t{0x10ull} + s1;
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shr_c<16>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_2913<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2913(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x11, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xffull} < s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return b_2924<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_291d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_291d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x91, 0x82, 0x01, 0x91, 0x1c}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x91, 0x82, 0x01, 0x91, 0x1c}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = uint256_t{0x8ull} + s1;
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shr_c<8>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_2924<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2924(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x11, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xfull} < s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return b_2935<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_292e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_292e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x91, 0x82, 0x01, 0x91, 0x1c}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x91, 0x82, 0x01, 0x91, 0x1c}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = uint256_t{0x4ull} + s1;
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shr_c<4>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_2935<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2935(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x11, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x3ull} < s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return b_2946<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_293f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_293f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x91, 0x82, 0x01, 0x91, 0x1c}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x91, 0x82, 0x01, 0x91, 0x1c}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = uint256_t{0x2ull} + s1;
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shr_c<2>(s0);
            top[-1] = t1;
            top[0] = t2;
            MONAD_AOT_TAIL return b_2946<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2946(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x11, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x1ull} < s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return b_2956<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2950<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2950(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x82, 0x01, 0x91, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x82, 0x01, 0x91, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x1ull};
            top[-1] = t1;
            MONAD_AOT_TAIL return b_2956<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2956(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_2963<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_295d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_295d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x82, 0x01, 0x91, 0x50}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x82, 0x01, 0x91, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x1ull};
            top[-1] = t1;
            MONAD_AOT_TAIL return b_2963<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2963(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x84, 0x81, 0x10, 0x15, 0x61, 0x57}, 6, 1));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x84, 0x81, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = aot::from_bool(s1 < s5);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            top += -1;
            if (j7) { MONAD_AOT_TAIL return b_296f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_296d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_296d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x83}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x83}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[0] = m4;
            MONAD_AOT_TAIL return b_296f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_296f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x81, 0x03, 0x90, 0x50, 0x85, 0x81, 0x1c, 0x5f, 0x82, 0x11, 0x84, 0x16, 0x15, 0x61, 0x57}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x81, 0x03, 0x90, 0x50, 0x85, 0x81, 0x1c, 0x5f, 0x82, 0x11, 0x84, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s0 - s4;
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = aot::shr(t1, s5);
            uint256_t const t3 = aot::from_bool(uint256_t{0x0ull} < t1);
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = s2 & t3;
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            bool const j16 = aot::nonzero(t5);
            top[0] = t1;
            top[1] = t2;
            top += 1;
            if (j16) { MONAD_AOT_TAIL return b_29bd<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2982<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2982(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x81, 0x01, 0x90, 0x50, 0x80, 0x60, 0x87, 0x1b, 0x03, 0x61, 0x57}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x81, 0x01, 0x90, 0x50, 0x80, 0x60, 0x87, 0x1b, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x1ull};
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = aot::shl(s5, uint256_t{0x1ull});
            uint256_t const t3 = t2 - t1;
            bool const j11 = aot::nonzero(t3);
            top[0] = t1;
            if (j11) { MONAD_AOT_TAIL return b_29bd<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2992<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2992(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x60, 0x90, 0x81, 0x01, 0x90, 0x7f, 0x86, 0x01, 0x1b}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x60, 0x90, 0x81, 0x01, 0x90, 0x7f, 0x86, 0x01, 0x1b}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = uint256_t{0x1ull} + s1;
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = s5 + uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::shl(t2, uint256_t{0x1ull});
            top[-1] = t1;
            top[0] = t3;
            MONAD_AOT_TAIL return b_29bd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_29bd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x85, 0x1b, 0x82, 0x10, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x85, 0x1b, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::shl(s4, uint256_t{0x1ull});
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::from_bool(s1 < t1);
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return b_29cb<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_29c8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_29c8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_29cb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x93, 0x1b, 0x90, 0x92, 0x01, 0x94, 0x93, 0x50, 0x50, 0x50, 0x50, 0x56}, 8, 0));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x93, 0x1b, 0x90, 0x92, 0x01, 0x94, 0x93, 0x50, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl(s4, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s1 + t1;
            uint256_t const &s7 = top[-7];
            uint64_t const jt = aot::jump_offset(s7);
            top[-7] = t2;
            top += -7;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_29d9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x80, 0x80, 0x60, 0x81, 0x73, 0x89, 0x16, 0x15, 0x61, 0x57}, 4, 7));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x80, 0x80, 0x60, 0x81, 0x73, 0x89, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j11 = aot::nonzero(t2);
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top[3] = uint256_t{0x0ull};
            top[4] = uint256_t{0x9ull};
            top[5] = uint256_t{0x0ull};
            top += 5;
            if (j11) { MONAD_AOT_TAIL return b_2a01<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_29fc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_29fc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x88, 0x61, 0x56}, 9, 2));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x88, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[1] = m8;
            top += 1;
            MONAD_AOT_TAIL return b_2a03<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2a01(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x33}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x33}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_2a03<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2a03(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x90, 0x81, 0x16, 0x82, 0x52, 0x60, 0x80, 0x83, 0x01, 0x93, 0x90, 0x93, 0x52, 0x60, 0x91, 0x82, 0x01, 0x5f, 0x90, 0x81, 0x20, 0x91, 0x8a, 0x16, 0x81, 0x52, 0x92, 0x52, 0x81, 0x20, 0x54, 0x91, 0x50, 0x81, 0x90, 0x03, 0x61, 0x57}, 9, 3));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x90, 0x81, 0x16, 0x82, 0x52, 0x60, 0x80, 0x83, 0x01, 0x93, 0x90, 0x93, 0x52, 0x60, 0x91, 0x82, 0x01, 0x5f, 0x90, 0x81, 0x20, 0x91, 0x8a, 0x16, 0x81, 0x52, 0x92, 0x52, 0x81, 0x20, 0x54, 0x91, 0x50, 0x81, 0x90, 0x03, 0x61, 0x57}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s0;
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, t1);
            uint256_t const t2 = s1 + uint256_t{0x20ull};
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t2, s2);
            uint256_t const t3 = uint256_t{0x40ull} + s1;
            auto const h22 = aot::sha3_any<traits>(ctx, gas, uint256_t{0x0ull}, t3);
            gas = ctx->gas_remaining;
            uint256_t const &s8 = top[-8];
            uint256_t const t4 = s8 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t4);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, h22);
            uint256_t const t5 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t6 = aot::sload<traits>(ctx, gas, t5);
            uint256_t const t7 = uint256_t{0x0ull} - t6;
            bool const j39 = aot::nonzero(t7);
            top[-3] = t6;
            top += -3;
            if (j39) { MONAD_AOT_TAIL return b_2a78<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2a43<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2a43(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2af9ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2a78(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x87, 0x16, 0x15, 0x80, 0x15, 0x61, 0x57}, 7, 3));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x87, 0x16, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s6 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j8 = aot::nonzero(t3);
            top[1] = t2;
            top += 1;
            if (j8) { MONAD_AOT_TAIL return b_2aa0<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2a97<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2a97(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x60, 0x60, 0x82, 0x90, 0x1c, 0x14}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x60, 0x60, 0x82, 0x90, 0x1c, 0x14}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<255>(s1);
            uint256_t const t2 = aot::from_bool(t1 == uint256_t{0x1ull});
            top[0] = t2;
            MONAD_AOT_TAIL return b_2aa0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2aa0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_2adb<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2aa6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2aa6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2afaull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2adb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x87, 0x16, 0x61, 0x57}, 7, 2));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x87, 0x16, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s6 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_2afa<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2af7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2af7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x33, 0x96, 0x50}, 7, 1));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x33, 0x96, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            top[-6] = t1;
            MONAD_AOT_TAIL return b_2afa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2afa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x66, 0x60, 0x82, 0x90, 0x1c, 0x16, 0x60, 0x60, 0x83, 0x90, 0x1c, 0x16, 0x1b, 0x5f, 0x61, 0x83, 0x83, 0x61, 0x56}, 1, 6));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x66, 0x60, 0x82, 0x90, 0x1c, 0x16, 0x60, 0x60, 0x83, 0x90, 0x1c, 0x16, 0x1b, 0x5f, 0x61, 0x83, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shr_c<9>(s0);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffull};
            uint256_t const t3 = aot::shr_c<1>(s0);
            uint256_t const t4 = t3 & uint256_t{0xffull};
            uint256_t const t5 = aot::shl(t4, t2);
            uint256_t const m0 = s0;
            top[1] = t5;
            top[2] = uint256_t{0x0ull};
            top[3] = uint256_t{0x2b1cull};
            top[4] = m0;
            top[5] = t5;
            top += 5;
            MONAD_AOT_TAIL return b_3216<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b1c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x82, 0x60, 0x16, 0x60, 0x03, 0x61, 0x57}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x82, 0x60, 0x16, 0x60, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = uint256_t{0x1ull} & s3;
            uint256_t const t2 = uint256_t{0x1ull} - t1;
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2b83); }
            MONAD_AOT_TAIL return b_2b2a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b2a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x87, 0x13, 0x15, 0x61, 0x57}, 7, 2));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x87, 0x13, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s6));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j5 = aot::nonzero(t2);
            if (j5) { MONAD_AOT_TAIL return b_2b54<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2b32<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b32(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x87, 0x64, 0x88, 0x61, 0x56}, 7, 5));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x87, 0x64, 0x88, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[1] = uint256_t{0x2b41ull};
            top[2] = m6;
            top[3] = uint256_t{0xe8d4a51000ull};
            top[4] = m5;
            top += 4;
            MONAD_AOT_TAIL return b_3183<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b41(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x94, 0x50, 0x61, 0x85, 0x83, 0x61, 0x56}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x94, 0x50, 0x61, 0x85, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-5] = m0;
            top[0] = uint256_t{0x2b4dull};
            top[1] = m0;
            top[2] = m2;
            top += 2;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b4d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x50, 0x61, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top += -1;
            MONAD_AOT_TAIL return b_2bae<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b54(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x85, 0x61, 0x64, 0x89, 0x61, 0x56}, 7, 5));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x85, 0x61, 0x64, 0x89, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[1] = m5;
            top[2] = uint256_t{0x2b64ull};
            top[3] = uint256_t{0xe8d4a51000ull};
            top[4] = m6;
            top += 4;
            MONAD_AOT_TAIL return b_377b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b64(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x2b6eull};
            top[0] = m1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_37c6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b6e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x94, 0x50, 0x61, 0x85, 0x61, 0x56}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x94, 0x50, 0x61, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-5] = m0;
            top[0] = uint256_t{0x2b79ull};
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_3641<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2b79(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x90, 0x83, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x90, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[0] = uint256_t{0x2b4dull};
            top[1] = m0;
            top[2] = m2;
            top += 2;
            MONAD_AOT_TAIL return b_373e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b8f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x84, 0x83, 0x61, 0x56}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x84, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = uint256_t{0x2b4dull};
            top[2] = m3;
            top[3] = m1;
            top += 3;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2bae(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x87, 0x13, 0x80, 0x15, 0x61, 0x57}, 7, 3));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x87, 0x13, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::from_bool(slt(uint256_t{0x0ull}, s6));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return b_2bbc<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2bb8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2bb8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x80, 0x82, 0x11}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x80, 0x82, 0x11}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < s2);
            top[0] = t1;
            MONAD_AOT_TAIL return b_2bbc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2bbc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return b_2bf7<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2bc2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2bc2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2afcull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2bf7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x83, 0x83, 0x83, 0x61, 0x56}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x83, 0x83, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x2c02ull};
            top[2] = m2;
            top[3] = m1;
            top[4] = m0;
            top += 4;
            MONAD_AOT_TAIL return b_32d2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2c02(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x61, 0x82, 0x60, 0x60, 0x60, 0x61, 0x56}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x61, 0x82, 0x60, 0x60, 0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-1] = m0;
            top[0] = uint256_t{0x2c13ull};
            top[1] = m2;
            top[2] = uint256_t{0x38ull};
            top[3] = uint256_t{0x8ull};
            top[4] = uint256_t{0x1ull};
            top += 4;
            MONAD_AOT_TAIL return b_28b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2c13(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x50, 0x81, 0x67, 0x60, 0x85, 0x90, 0x1c, 0x16, 0x03, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x50, 0x81, 0x67, 0x60, 0x85, 0x90, 0x1c, 0x16, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::shr_c<1>(s3);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull};
            uint256_t const &s0 = top[0];
            uint256_t const t3 = t2 - s0;
            bool const j12 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[-2] = m0;
            top += -1;
            if (j12) { MONAD_AOT_TAIL return b_2c60<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2c2b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2c2b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x61, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdcab82e200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x2affull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2c60(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x60, 0x60, 0x5f, 0x61, 0x56}, 1, 6));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x60, 0x60, 0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x2c6eull};
            top[2] = m0;
            top[3] = uint256_t{0x38ull};
            top[4] = uint256_t{0x8ull};
            top[5] = uint256_t{0x0ull};
            top += 5;
            MONAD_AOT_TAIL return b_28b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2c6e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x99, 0x8a, 0x16, 0x5f, 0x90, 0x81, 0x52, 0x60, 0x60, 0x90, 0x81, 0x52, 0x60, 0x80, 0x83, 0x20, 0x9b, 0x90, 0x9c, 0x16, 0x82, 0x52, 0x99, 0x90, 0x99, 0x52, 0x98, 0x90, 0x97, 0x20, 0x7f, 0x90, 0x92, 0x16, 0x60, 0x91, 0x90, 0x91, 0x1b, 0x17, 0x60, 0x97, 0x90, 0x97, 0x1b, 0x96, 0x90, 0x96, 0x17, 0x42, 0x60, 0x1b, 0x17, 0x90, 0x95, 0x55, 0x94, 0x92, 0x50, 0x50, 0x50, 0x56}, 11, 5));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x99, 0x8a, 0x16, 0x5f, 0x90, 0x81, 0x52, 0x60, 0x60, 0x90, 0x81, 0x52, 0x60, 0x80, 0x83, 0x20, 0x9b, 0x90, 0x9c, 0x16, 0x82, 0x52, 0x99, 0x90, 0x99, 0x52, 0x98, 0x90, 0x97, 0x20, 0x7f, 0x90, 0x92, 0x16, 0x60, 0x91, 0x90, 0x91, 0x1b, 0x17, 0x60, 0x97, 0x90, 0x97, 0x1b, 0x96, 0x90, 0x96, 0x17, 0x42, 0x60, 0x1b, 0x17, 0x90, 0x95, 0x55, 0x94, 0x92, 0x50, 0x50, 0x50, 0x56}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s9 = top[-9];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s9;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x9ull});
            uint256_t const t2 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const &s8 = top[-8];
            uint256_t const t3 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s8;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t2);
            uint256_t const t4 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const &s3 = top[-3];
            uint256_t const t5 = s3 & uint256_t{0x1ull, 0x0ull, 0xfffffffc00000000ull, 0xffffffffffffffffull};
            uint256_t const &s2 = top[-2];
            uint256_t const t6 = aot::shl_c<1>(s2);
            uint256_t const t7 = t6 | t5;
            uint256_t const &s0 = top[0];
            uint256_t const t8 = aot::shl_c<65>(s0);
            uint256_t const t9 = t8 | t7;
            uint256_t const t10 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const t11 = aot::shl_c<129>(t10);
            uint256_t const t12 = t11 | t9;
            aot::sstore<traits>(ctx, gas, t4, t12, (aot::gas_of<traits>({0x94, 0x92, 0x50, 0x50, 0x50, 0x56}) + 0));
            uint256_t const &s10 = top[-10];
            uint64_t const jt = aot::jump_offset(s10);
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-10] = m5;
            top[-9] = m4;
            top += -9;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2cf7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x84, 0x84, 0x61, 0x56}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x84, 0x84, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[1] = uint256_t{0x2d00ull};
            top[2] = m3;
            top[3] = m2;
            top += 3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3331);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d10(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x84, 0x84, 0x61, 0x56}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x84, 0x84, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[1] = uint256_t{0x2d00ull};
            top[2] = m3;
            top[3] = m2;
            top += 3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x340c);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d5b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x61, 0x92, 0x50, 0x7f, 0x90, 0x5f, 0x90, 0xa1}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x61, 0x92, 0x50, 0x7f, 0x90, 0x5f, 0x90, 0xa1}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const k9_1 = uint256_t{0x0ull};
            uint256_t const k9_2 = uint256_t{0x513add0fbb27bcd7ull, 0x8fd7ba9f85e0c101ull, 0x442f6a1e760ae509ull, 0xe41708b2641eb1f7ull};
            ctx->gas_remaining = gas;
            runtime::log1<traits>(ctx, &t1, &k9_1, &k9_2);
            gas = ctx->gas_remaining;
            top[-1] = uint256_t{0xffffull};
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2d88);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2d8f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x85, 0x87, 0x61, 0xf1, 0x90, 0x50, 0x80, 0x61, 0x57}, 2, 8));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x85, 0x87, 0x61, 0xf1, 0x90, 0x50, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            auto const c9 = aot::call<traits>(ctx, gas, uint256_t{0xc350ull}, s1, s0, uint256_t{0x0ull}, uint256_t{0x0ull}, uint256_t{0x0ull}, uint256_t{0x0ull}, (aot::gas_of<traits>({0x90, 0x50, 0x80, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            bool const j14 = aot::nonzero(c9);
            top[1] = c9;
            top += 1;
            if (j14) { MONAD_AOT_TAIL return b_28ae<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2da2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2da2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x62, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x62, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdee51a8a00000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x1155aull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2dd8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x73, 0x83, 0x16, 0x01, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x73, 0x83, 0x16, 0x01, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = t1 + uint256_t{0x364fa4bc1ca64812ull, 0x7a7df0848d2f6d90ull, 0xffffffff32a01dc3ull, 0xffffffffffffffffull};
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return b_2f12<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2e16<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e16(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x81, 0x90, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x86, 0x5a, 0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}, 1, 10));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x81, 0x90, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x86, 0x5a, 0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x70a0823100000000ull});
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t3 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = uint256_t{0x24ull} + t1;
            uint256_t const t5 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t6 = t4 - t5;
            uint256_t const t7 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k27_1 = uint256_t{0xc9b05b43e359b7eeull, 0x85820f7b72d0926full, 0xcd5fe23cull, 0x0ull};
            uint256_t const k27_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r27;
            runtime::staticcall<traits>(ctx, &r27, &t7, &k27_1, &t5, &t6, &t5, &k27_5, (aot::gas_of<traits>({0x15, 0x80, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(r27));
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            bool const j32 = aot::nonzero(t9);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = m0;
            top[2] = uint256_t{0xc9b05b43e359b7eeull, 0x85820f7b72d0926full, 0xcd5fe23cull, 0x0ull};
            top[3] = uint256_t{0x70a08231ull};
            top[4] = t4;
            top[5] = t8;
            top += 5;
            if (j32) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2e7d); }
            MONAD_AOT_TAIL return b_2e76<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e76(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const k3_0 = uint256_t{0x0ull};
            uint256_t const k3_1 = uint256_t{0x0ull};
            ctx->gas_remaining = gas;
            runtime::returndatacopy<traits>(ctx, &k3_0, &k3_1, &t1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, t2);
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ea8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x73, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x82, 0x90, 0x52, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x73, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x82, 0x90, 0x52, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xf3fef3a300000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0xc9b05b43e359b7eeull, 0x85820f7b72d0926full, 0xcd5fe23cull, 0x0ull});
            uint256_t const t3 = t1 + uint256_t{0x24ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t3, s0);
            uint256_t const t4 = uint256_t{0x44ull} + t1;
            top[1] = uint256_t{0x2c186f3611aeafa6ull, 0x75cebf0eb9ed34aeull, 0xf047ab4cull, 0x0ull};
            top[2] = uint256_t{0xf3fef3a3ull};
            top[3] = t4;
            top += 3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1f51);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2f12(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x73, 0x83, 0x16, 0x01, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x73, 0x83, 0x16, 0x01, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t2 = t1 + uint256_t{0x3f32e12d2a6f6278ull, 0xe59806cc0d194cc0ull, 0xffffffff6e83117full, 0xffffffffffffffffull};
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return b_1f7f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2f50<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2f50(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x81, 0x90, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x86, 0x5a, 0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}, 1, 10));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x30, 0x60, 0x82, 0x01, 0x52, 0x81, 0x90, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x86, 0x5a, 0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x70a0823100000000ull});
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t3 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = uint256_t{0x24ull} + t1;
            uint256_t const t5 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t6 = t4 - t5;
            uint256_t const t7 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k27_1 = uint256_t{0xc0cd1ed2d5909d88ull, 0x1a67f933f2e6b33full, 0x917cee80ull, 0x0ull};
            uint256_t const k27_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r27;
            runtime::staticcall<traits>(ctx, &r27, &t7, &k27_1, &t5, &t6, &t5, &k27_5, (aot::gas_of<traits>({0x15, 0x80, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(r27));
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            bool const j32 = aot::nonzero(t9);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = m0;
            top[2] = uint256_t{0xc0cd1ed2d5909d88ull, 0x1a67f933f2e6b33full, 0x917cee80ull, 0x0ull};
            top[3] = uint256_t{0x70a08231ull};
            top[4] = t4;
            top[5] = t8;
            top += 5;
            if (j32) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2fb7); }
            MONAD_AOT_TAIL return b_2fb0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2fb0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const k3_0 = uint256_t{0x0ull};
            uint256_t const k3_1 = uint256_t{0x0ull};
            ctx->gas_remaining = gas;
            runtime::returndatacopy<traits>(ctx, &k3_0, &k3_1, &t1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, t2);
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2fe2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x73, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x82, 0x90, 0x52, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x73, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x01, 0x82, 0x90, 0x52, 0x73, 0x90, 0x63, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xf3fef3a300000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0xc0cd1ed2d5909d88ull, 0x1a67f933f2e6b33full, 0x917cee80ull, 0x0ull});
            uint256_t const t3 = t1 + uint256_t{0x24ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t3, s0);
            uint256_t const t4 = uint256_t{0x44ull} + t1;
            top[1] = uint256_t{0x2c186f3611aeafa6ull, 0x75cebf0eb9ed34aeull, 0xf047ab4cull, 0x0ull};
            top[2] = uint256_t{0xf3fef3a3ull};
            top[3] = t4;
            top += 3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1f51);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_304c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x60, 0x51, 0x7f, 0x81, 0x52, 0x73, 0x84, 0x16, 0x60, 0x82, 0x01, 0x52, 0x82, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5f, 0x60, 0x83, 0x5f, 0x89, 0x5a, 0xf1, 0x3d, 0x15, 0x60, 0x3d, 0x11, 0x60, 0x5f, 0x51, 0x14, 0x16, 0x17, 0x16, 0x91, 0x50, 0x50, 0x80, 0x61, 0x57}, 3, 9));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x60, 0x51, 0x7f, 0x81, 0x52, 0x73, 0x84, 0x16, 0x60, 0x82, 0x01, 0x52, 0x82, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5f, 0x60, 0x83, 0x5f, 0x89, 0x5a, 0xf1, 0x3d, 0x15, 0x60, 0x3d, 0x11, 0x60, 0x5f, 0x51, 0x14, 0x16, 0x17, 0x16, 0x91, 0x50, 0x50, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xa9059cbb00000000ull});
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = t1 + uint256_t{0x24ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t4, s0);
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xf1, 0x3d, 0x15, 0x60, 0x3d, 0x11, 0x60, 0x5f, 0x51, 0x14, 0x16, 0x17, 0x16, 0x91, 0x50, 0x50, 0x80, 0x61, 0x57}) + 0))};
            uint256_t const &s2 = top[-2];
            auto const c26 = aot::call<traits>(ctx, gas, t5, s2, uint256_t{0x0ull}, t1, uint256_t{0x44ull}, uint256_t{0x0ull}, uint256_t{0x20ull}, (aot::gas_of<traits>({0x3d, 0x15, 0x60, 0x3d, 0x11, 0x60, 0x5f, 0x51, 0x14, 0x16, 0x17, 0x16, 0x91, 0x50, 0x50, 0x80, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t6 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t9 = aot::from_bool(uint256_t{0x1full} < t8);
            uint256_t const t10 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const t11 = aot::from_bool(t10 == uint256_t{0x1ull});
            uint256_t const t12 = t11 & t9;
            uint256_t const t13 = t12 | t7;
            uint256_t const t14 = t13 & c26;
            bool const j44 = aot::nonzero(t14);
            top[1] = t14;
            top += 1;
            if (j44) { MONAD_AOT_TAIL return b_30ec<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_30b6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_30b6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x62, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x62, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xdee51a8a00000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x1155aull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_30ec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint64_t const jt = aot::jump_offset(s4);
            top += -5;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_30f2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x66, 0x60, 0x84, 0x90, 0x1c, 0x16, 0x60, 0x60, 0x85, 0x90, 0x1c, 0x16, 0x1b, 0x80, 0x82, 0x03, 0x61, 0x57}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x66, 0x60, 0x84, 0x90, 0x1c, 0x16, 0x60, 0x60, 0x85, 0x90, 0x1c, 0x16, 0x1b, 0x80, 0x82, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<73>(s1);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffull};
            uint256_t const t3 = aot::shr_c<65>(s1);
            uint256_t const t4 = t3 & uint256_t{0xffull};
            uint256_t const t5 = aot::shl(t4, t2);
            uint256_t const t6 = uint256_t{0x0ull} - t5;
            bool const j19 = aot::nonzero(t6);
            top[1] = uint256_t{0x0ull};
            top[2] = t5;
            top += 2;
            if (j19) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x311a); }
            MONAD_AOT_TAIL return b_3112<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3112(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x91, 0x50, 0x50, 0x61, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x91, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-1] = uint256_t{0x0ull};
            top += -1;
            MONAD_AOT_TAIL return b_1df5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_315f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3168);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3177(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x93, 0x50}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x93, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-3] = m0;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x317a);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3183(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x82, 0x7f, 0x04, 0x84, 0x11, 0x83, 0x02, 0x15, 0x82, 0x02, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x82, 0x7f, 0x04, 0x84, 0x11, 0x83, 0x02, 0x15, 0x82, 0x02, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::udiv(uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull}, s1);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = aot::from_bool(t1 < s2);
            uint256_t const t3 = aot::mul(s1, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const &s0 = top[0];
            uint256_t const t5 = aot::mul(s0, t4);
            bool const j13 = aot::nonzero(t5);
            top[1] = uint256_t{0x0ull};
            top += 1;
            if (j13) { MONAD_AOT_TAIL return b_31b6<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_31b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_31b3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_31b6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x91, 0x02, 0x81, 0x81, 0x06, 0x15, 0x15, 0x91, 0x90, 0x04, 0x01, 0x90, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x91, 0x02, 0x81, 0x81, 0x06, 0x15, 0x15, 0x91, 0x90, 0x04, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mul(s3, s2);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::umod(t1, s1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::udiv(t1, s1);
            uint256_t const t6 = t5 + t4;
            uint256_t const &s4 = top[-4];
            uint64_t const jt = aot::jump_offset(s4);
            top[-4] = t6;
            top += -4;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_31c5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x61, 0x60, 0x85, 0x90, 0x1c, 0x16, 0x60, 0x60, 0x86, 0x90, 0x1c, 0x16, 0x1b, 0x80, 0x84, 0x10, 0x15, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x61, 0x60, 0x85, 0x90, 0x1c, 0x16, 0x60, 0x60, 0x86, 0x90, 0x1c, 0x16, 0x1b, 0x80, 0x84, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::shr_c<208>(s2);
            uint256_t const t2 = t1 & uint256_t{0x3ffull};
            uint256_t const t3 = aot::shr_c<200>(s2);
            uint256_t const t4 = t3 & uint256_t{0xffull};
            uint256_t const t5 = aot::shl(t4, t2);
            uint256_t const &s1 = top[-1];
            uint256_t const t6 = aot::from_bool(s1 < t5);
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            bool const j20 = aot::nonzero(t7);
            top[1] = uint256_t{0x0ull};
            top[2] = t5;
            top += 2;
            if (j20) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x31e9); }
            MONAD_AOT_TAIL return b_31e1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_31e1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x91, 0x50, 0x50, 0x61, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x91, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[-1] = uint256_t{0x0ull};
            top += -1;
            MONAD_AOT_TAIL return b_320f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3204(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            MONAD_AOT_TAIL return b_320f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_320f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x93, 0x92, 0x50, 0x50, 0x50, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x93, 0x92, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint64_t const jt = aot::jump_offset(s4);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-4] = m0;
            top += -4;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3216(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x60, 0x83, 0x90, 0x1c, 0x64, 0x16, 0x42, 0x03, 0x61, 0x61, 0x60, 0x86, 0x90, 0x1c, 0x16, 0x84, 0x02, 0x04, 0x80, 0x84, 0x01, 0x60, 0x86, 0x90, 0x1c, 0x66, 0x16, 0x60, 0x87, 0x90, 0x1c, 0x60, 0x16, 0x1b, 0x60, 0x87, 0x90, 0x1c, 0x62, 0x16, 0x61, 0x85, 0x85, 0x61, 0x56}, 2, 10));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x60, 0x83, 0x90, 0x1c, 0x64, 0x16, 0x42, 0x03, 0x61, 0x61, 0x60, 0x86, 0x90, 0x1c, 0x16, 0x84, 0x02, 0x04, 0x80, 0x84, 0x01, 0x60, 0x86, 0x90, 0x1c, 0x66, 0x16, 0x60, 0x87, 0x90, 0x1c, 0x60, 0x16, 0x1b, 0x60, 0x87, 0x90, 0x1c, 0x62, 0x16, 0x61, 0x85, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::shr_c<129>(s1);
            uint256_t const t2 = uint256_t{0x1ffffffffull} & t1;
            uint256_t const t3 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const t4 = t3 - t2;
            uint256_t const t5 = aot::shr_c<162>(s1);
            uint256_t const t6 = t5 & uint256_t{0x3fffull};
            uint256_t const &s0 = top[0];
            uint256_t const t7 = aot::mul(s0, t6);
            uint256_t const t8 = aot::udiv(t7, uint256_t{0x2710ull});
            uint256_t const t9 = s0 + t8;
            uint256_t const t10 = aot::shr_c<73>(s1);
            uint256_t const t11 = uint256_t{0xffffffffffffffull} & t10;
            uint256_t const t12 = aot::shr_c<65>(s1);
            uint256_t const t13 = uint256_t{0xffull} & t12;
            uint256_t const t14 = aot::shl(t13, t11);
            uint256_t const t15 = aot::shr_c<176>(s1);
            uint256_t const t16 = uint256_t{0xffffffull} & t15;
            top[1] = uint256_t{0x0ull};
            top[2] = t4;
            top[3] = t8;
            top[4] = t9;
            top[5] = t14;
            top[6] = t16;
            top[7] = uint256_t{0x3262ull};
            top[8] = t4;
            top[9] = t8;
            top += 9;
            MONAD_AOT_TAIL return b_3751<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3262(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x326cull};
            top[0] = m1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_3768<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_326c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x3276ull};
            top[0] = m1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_3677<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3276(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x93, 0x50, 0x80, 0x84, 0x11, 0x15, 0x61, 0x57}, 5, 1));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x93, 0x50, 0x80, 0x84, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j8 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            top[-4] = m0;
            top += -1;
            if (j8) { MONAD_AOT_TAIL return b_3284<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3281<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3281(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x93, 0x50}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x93, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-3] = m0;
            MONAD_AOT_TAIL return b_3284<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3284(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x87, 0x90, 0x1c, 0x16, 0x60, 0x60, 0x88, 0x90, 0x1c, 0x16, 0x1b, 0x92, 0x50, 0x82, 0x84, 0x10, 0x15, 0x61, 0x57}, 6, 4));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x87, 0x90, 0x1c, 0x16, 0x60, 0x60, 0x88, 0x90, 0x1c, 0x16, 0x1b, 0x92, 0x50, 0x82, 0x84, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = aot::shr_c<208>(s5);
            uint256_t const t2 = t1 & uint256_t{0x3ffull};
            uint256_t const t3 = aot::shr_c<200>(s5);
            uint256_t const t4 = t3 & uint256_t{0xffull};
            uint256_t const t5 = aot::shl(t4, t2);
            uint256_t const &s3 = top[-3];
            uint256_t const t6 = aot::from_bool(s3 < t5);
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            bool const j21 = aot::nonzero(t7);
            top[-2] = t5;
            if (j21) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x32ab); }
            MONAD_AOT_TAIL return b_32a1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_32a1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x93, 0x50, 0x50, 0x50, 0x50, 0x61, 0x56}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x93, 0x50, 0x50, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-3] = m2;
            top += -3;
            MONAD_AOT_TAIL return b_1df5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_32c8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x93, 0x50, 0x50, 0x50, 0x50, 0x61, 0x56}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x93, 0x50, 0x50, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-3] = m2;
            top += -3;
            MONAD_AOT_TAIL return b_1df5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_32d2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x60, 0x85, 0x90, 0x1c, 0x16, 0x83, 0x02, 0x04, 0x82, 0x01, 0x60, 0x84, 0x90, 0x1c, 0x61, 0x16, 0x60, 0x85, 0x90, 0x1c, 0x60, 0x16, 0x1b, 0x80, 0x82, 0x10, 0x15, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x60, 0x85, 0x90, 0x1c, 0x16, 0x83, 0x02, 0x04, 0x82, 0x01, 0x60, 0x84, 0x90, 0x1c, 0x61, 0x16, 0x60, 0x85, 0x90, 0x1c, 0x60, 0x16, 0x1b, 0x80, 0x82, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::shr_c<162>(s2);
            uint256_t const t2 = t1 & uint256_t{0x3fffull};
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::mul(s1, t2);
            uint256_t const t4 = aot::udiv(t3, uint256_t{0x2710ull});
            uint256_t const t5 = s1 + t4;
            uint256_t const t6 = aot::shr_c<208>(s2);
            uint256_t const t7 = uint256_t{0x3ffull} & t6;
            uint256_t const t8 = aot::shr_c<200>(s2);
            uint256_t const t9 = uint256_t{0xffull} & t8;
            uint256_t const t10 = aot::shl(t9, t7);
            uint256_t const t11 = aot::from_bool(t5 < t10);
            uint256_t const t12 = aot::from_bool(!aot::nonzero(t11));
            bool const j31 = aot::nonzero(t12);
            top[1] = t5;
            top[2] = t10;
            top += 2;
            if (j31) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3304); }
            MONAD_AOT_TAIL return b_32fe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_32fe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x50, 0x61, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            MONAD_AOT_TAIL return b_320f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3320(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x91, 0x50}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x91, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m0;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3323);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_332c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x61, 0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top += -1;
            MONAD_AOT_TAIL return b_320f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3348(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x60, 0x89, 0x90, 0x1c, 0x16, 0x94, 0x50, 0x61, 0x60, 0x89, 0x90, 0x1c, 0x16, 0x93, 0x50, 0x5f, 0x92, 0x50, 0x80, 0x91, 0x50, 0x61, 0x56}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x60, 0x89, 0x90, 0x1c, 0x16, 0x94, 0x50, 0x61, 0x60, 0x89, 0x90, 0x1c, 0x16, 0x93, 0x50, 0x5f, 0x92, 0x50, 0x80, 0x91, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::shr_c<4>(s7);
            uint256_t const t2 = t1 & uint256_t{0xffffull};
            uint256_t const t3 = aot::shr_c<36>(s7);
            uint256_t const t4 = t3 & uint256_t{0xffffull};
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-4] = t2;
            top[-3] = t4;
            top[-2] = uint256_t{0x0ull};
            top[-1] = m0;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3387);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_339c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x33a3ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x368a);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_33c1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x62, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x7f, 0x81, 0x52, 0x62, 0x60, 0x82, 0x01, 0x52, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xd50d751200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x11173ull});
            uint256_t const t3 = uint256_t{0x24ull} + t1;
            top[1] = t3;
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xac);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3423(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x60, 0x89, 0x90, 0x1c, 0x16, 0x94, 0x50, 0x61, 0x60, 0x89, 0x90, 0x1c, 0x16, 0x93, 0x50, 0x5f, 0x92, 0x50, 0x80, 0x91, 0x50, 0x61, 0x56}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x60, 0x89, 0x90, 0x1c, 0x16, 0x94, 0x50, 0x61, 0x60, 0x89, 0x90, 0x1c, 0x16, 0x93, 0x50, 0x5f, 0x92, 0x50, 0x80, 0x91, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::shr_c<4>(s7);
            uint256_t const t2 = t1 & uint256_t{0xffffull};
            uint256_t const t3 = aot::shr_c<36>(s7);
            uint256_t const t4 = t3 & uint256_t{0xffffull};
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-4] = t2;
            top[-3] = t4;
            top[-2] = uint256_t{0x0ull};
            top[-1] = m0;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3387);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3455(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x60, 0x8a, 0x90, 0x1c, 0x16, 0x95, 0x50, 0x61, 0x60, 0x8a, 0x90, 0x1c, 0x16, 0x94, 0x50, 0x81, 0x93, 0x50, 0x80, 0x92, 0x50, 0x61, 0x56}, 9, 3));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x60, 0x8a, 0x90, 0x1c, 0x16, 0x95, 0x50, 0x61, 0x60, 0x8a, 0x90, 0x1c, 0x16, 0x94, 0x50, 0x81, 0x93, 0x50, 0x80, 0x92, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = aot::shr_c<36>(s8);
            uint256_t const t2 = t1 & uint256_t{0xffffull};
            uint256_t const t3 = aot::shr_c<68>(s8);
            uint256_t const t4 = t3 & uint256_t{0xffffull};
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-5] = t2;
            top[-4] = t4;
            top[-3] = m1;
            top[-2] = m0;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3494);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_34aa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x33a3ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x368a);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_34b1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x35, 0x73, 0x81, 0x16, 0x81, 0x14, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x35, 0x73, 0x81, 0x16, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = aot::from_bool(t1 == t2);
            bool const j9 = aot::nonzero(t3);
            top[1] = t1;
            top += 1;
            if (j9) { MONAD_AOT_TAIL return b_34d4<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_34d1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_34d1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_34d4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x90, 0x50, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x90, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top += -2;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_34d9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x5f, 0x83, 0x60, 0x84, 0x01, 0x12, 0x61, 0x57}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x5f, 0x83, 0x60, 0x84, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x1full};
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::from_bool(slt(t1, s1));
            bool const j9 = aot::nonzero(t2);
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top += 2;
            if (j9) { MONAD_AOT_TAIL return b_34e9<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_34e6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_34e6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_34e9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x81, 0x35, 0x67, 0x81, 0x11, 0x15, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x81, 0x35, 0x67, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::calldataload(ctx, s2);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j9 = aot::nonzero(t3);
            top[0] = t1;
            if (j9) { MONAD_AOT_TAIL return b_3500<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_34fd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_34fd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3500(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x83, 0x01, 0x91, 0x50, 0x83, 0x60, 0x82, 0x85, 0x01, 0x01, 0x11, 0x15, 0x61, 0x57}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x83, 0x01, 0x91, 0x50, 0x83, 0x60, 0x82, 0x85, 0x01, 0x01, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s2 + s0;
            uint256_t const t3 = t2 + uint256_t{0x20ull};
            uint256_t const &s3 = top[-3];
            uint256_t const t4 = aot::from_bool(s3 < t3);
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            bool const j15 = aot::nonzero(t5);
            top[-1] = t1;
            if (j15) { MONAD_AOT_TAIL return b_3517<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3514<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3514(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3517(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x50, 0x92, 0x90, 0x50, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x50, 0x92, 0x90, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint64_t const jt = aot::jump_offset(s4);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-4] = m1;
            top[-3] = m0;
            top += -3;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_351e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x60, 0x88, 0x8a, 0x03, 0x12, 0x15, 0x61, 0x57}, 2, 10));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x60, 0x88, 0x8a, 0x03, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 - s0;
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0xc0ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j15 = aot::nonzero(t3);
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top[3] = uint256_t{0x0ull};
            top[4] = uint256_t{0x0ull};
            top[5] = uint256_t{0x0ull};
            top[6] = uint256_t{0x0ull};
            top[7] = uint256_t{0x0ull};
            top += 7;
            if (j15) { MONAD_AOT_TAIL return b_3534<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3531<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3531(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3534(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x88, 0x61, 0x56}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x88, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[1] = uint256_t{0x353dull};
            top[2] = m7;
            top += 2;
            MONAD_AOT_TAIL return b_34b1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_353d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x96, 0x50, 0x60, 0x88, 0x01, 0x35, 0x95, 0x50, 0x60, 0x88, 0x01, 0x35, 0x94, 0x50, 0x61, 0x60, 0x89, 0x01, 0x61, 0x56}, 9, 2));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x96, 0x50, 0x60, 0x88, 0x01, 0x35, 0x95, 0x50, 0x60, 0x88, 0x01, 0x35, 0x94, 0x50, 0x61, 0x60, 0x89, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = s8 + uint256_t{0x20ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const t3 = s8 + uint256_t{0x40ull};
            uint256_t const t4 = aot::calldataload(ctx, t3);
            uint256_t const t5 = s8 + uint256_t{0x60ull};
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-7] = m0;
            top[-6] = t2;
            top[-5] = t4;
            top[0] = uint256_t{0x3559ull};
            top[1] = t5;
            top += 1;
            MONAD_AOT_TAIL return b_34b1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3559(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x93, 0x50, 0x61, 0x60, 0x89, 0x01, 0x61, 0x56}, 9, 2));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x93, 0x50, 0x61, 0x60, 0x89, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = s8 + uint256_t{0x80ull};
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-4] = m0;
            top[0] = uint256_t{0x3567ull};
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_34b1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3567(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x50, 0x60, 0x88, 0x01, 0x35, 0x67, 0x81, 0x11, 0x15, 0x61, 0x57}, 9, 2));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x50, 0x60, 0x88, 0x01, 0x35, 0x67, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = s8 + uint256_t{0xa0ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j12 = aot::nonzero(t4);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-3] = m0;
            top[0] = t2;
            if (j12) { MONAD_AOT_TAIL return b_3582<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_357f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_357f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3582(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x8a, 0x82, 0x8b, 0x01, 0x61, 0x56}, 10, 4));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x8a, 0x82, 0x8b, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s8 + s0;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[1] = uint256_t{0x358eull};
            top[2] = m9;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_34d9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_358e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x98, 0x9b, 0x97, 0x9a, 0x50, 0x95, 0x98, 0x50, 0x93, 0x96, 0x92, 0x95, 0x92, 0x93, 0x50, 0x50, 0x50, 0x56}, 13, 0));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x98, 0x9b, 0x97, 0x9a, 0x50, 0x95, 0x98, 0x50, 0x93, 0x96, 0x92, 0x95, 0x92, 0x93, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s12 = top[-12];
            uint64_t const jt = aot::jump_offset(s12);
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-12] = m9;
            top[-11] = m8;
            top[-10] = m7;
            top[-9] = m6;
            top[-8] = m5;
            top[-7] = m1;
            top[-6] = m0;
            top += -6;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_35b3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_35f3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3641(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x7f, 0x82, 0x03, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x7f, 0x82, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 - uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull};
            bool const j6 = aot::nonzero(t1);
            top[1] = uint256_t{0x0ull};
            top += 1;
            if (j6) { MONAD_AOT_TAIL return b_3671<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_366a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_366a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x3671ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3614);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3671(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x5f, 0x03, 0x90, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x5f, 0x03, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = uint256_t{0x0ull} - s1;
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t1;
            top += -2;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3677(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x82, 0x01, 0x80, 0x82, 0x11, 0x15, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x82, 0x01, 0x80, 0x82, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 + s0;
            uint256_t const t2 = aot::from_bool(t1 < s0);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j9 = aot::nonzero(t3);
            top[1] = t1;
            top += 1;
            if (j9) { MONAD_AOT_TAIL return b_1df5<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3683<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3683(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x1df5ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3614);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_36b7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x60, 0x82, 0x84, 0x03, 0x12, 0x15, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x60, 0x82, 0x84, 0x03, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 - s0;
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x20ull}));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j9 = aot::nonzero(t3);
            top[1] = uint256_t{0x0ull};
            top += 1;
            if (j9) { MONAD_AOT_TAIL return b_36c7<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_36c4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_36c4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x5f, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x5f, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_36c7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x51, 0x91, 0x90, 0x50, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x51, 0x91, 0x90, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top[-3] = t1;
            top += -3;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_36ce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x85, 0x16, 0x81, 0x52, 0x83, 0x60, 0x82, 0x01, 0x52, 0x60, 0x60, 0x82, 0x01, 0x52, 0x81, 0x60, 0x82, 0x01, 0x52, 0x81, 0x83, 0x60, 0x83, 0x01, 0x37, 0x5f, 0x81, 0x83, 0x01, 0x60, 0x90, 0x81, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x90, 0x92, 0x01, 0x7f, 0x16, 0x01, 0x01, 0x93, 0x92, 0x50, 0x50, 0x50, 0x56}, 6, 4));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x85, 0x16, 0x81, 0x52, 0x83, 0x60, 0x82, 0x01, 0x52, 0x60, 0x60, 0x82, 0x01, 0x52, 0x81, 0x60, 0x82, 0x01, 0x52, 0x81, 0x83, 0x60, 0x83, 0x01, 0x37, 0x5f, 0x81, 0x83, 0x01, 0x60, 0x90, 0x81, 0x01, 0x91, 0x90, 0x91, 0x52, 0x60, 0x90, 0x92, 0x01, 0x7f, 0x16, 0x01, 0x01, 0x93, 0x92, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s4 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, t1);
            uint256_t const t2 = s0 + uint256_t{0x20ull};
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, t2, s3);
            uint256_t const t3 = s0 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0x60ull});
            uint256_t const t4 = s0 + uint256_t{0x60ull};
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t4, s1);
            uint256_t const t5 = s0 + uint256_t{0x80ull};
            uint256_t const &s2 = top[-2];
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t5, &s2, &s1);
            gas = ctx->gas_remaining;
            uint256_t const t6 = s1 + s0;
            uint256_t const t7 = uint256_t{0x80ull} + t6;
            aot::mstore<traits>(ctx, gas, t7, uint256_t{0x0ull});
            uint256_t const t8 = s1 + uint256_t{0x1full};
            uint256_t const t9 = uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} & t8;
            uint256_t const t10 = t9 + s0;
            uint256_t const t11 = t10 + uint256_t{0x80ull};
            uint256_t const &s5 = top[-5];
            uint64_t const jt = aot::jump_offset(s5);
            top[-5] = t11;
            top += -5;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_373e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x81, 0x03, 0x81, 0x81, 0x11, 0x15, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x81, 0x03, 0x81, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const t2 = aot::from_bool(s0 < t1);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j9 = aot::nonzero(t3);
            top[1] = t1;
            top += 1;
            if (j9) { MONAD_AOT_TAIL return b_1df5<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_374a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_374a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x1df5ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3614);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3751(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x82, 0x02, 0x81, 0x15, 0x82, 0x82, 0x04, 0x84, 0x14, 0x17, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x82, 0x02, 0x81, 0x15, 0x82, 0x82, 0x04, 0x84, 0x14, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(s1, s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const t3 = aot::udiv(t1, s0);
            uint256_t const t4 = aot::from_bool(s1 == t3);
            uint256_t const t5 = t4 | t2;
            bool const j13 = aot::nonzero(t5);
            top[1] = t1;
            top += 1;
            if (j13) { MONAD_AOT_TAIL return b_1df5<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3761<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3761(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x1df5ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3614);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3768(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x82, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x82, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            bool const j4 = aot::nonzero(s1);
            top[1] = uint256_t{0x0ull};
            top += 1;
            if (j4) { MONAD_AOT_TAIL return b_3776<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_376f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_376f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x3776ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x368a);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3776(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x04, 0x90, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x04, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::udiv(s1, s2);
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top[-3] = t1;
            top += -3;
            if (MONAD_LIKELY(jt < 14435)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_377b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x82, 0x02, 0x5f, 0x82, 0x12, 0x7f, 0x84, 0x14, 0x16, 0x15, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x82, 0x02, 0x5f, 0x82, 0x12, 0x7f, 0x84, 0x14, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(s1, s0);
            uint256_t const t2 = aot::from_bool(slt(s0, uint256_t{0x0ull}));
            uint256_t const t3 = aot::from_bool(s1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t4 = t3 & t2;
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            bool const j13 = aot::nonzero(t5);
            top[1] = t1;
            top += 1;
            if (j13) { MONAD_AOT_TAIL return b_37b2<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_37ab<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_37ab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x37b2ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3614);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_37b2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x81, 0x05, 0x83, 0x14, 0x82, 0x15, 0x17, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x81, 0x05, 0x83, 0x14, 0x82, 0x15, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t r3;
            runtime::sdiv(&r3, &s0, &s1);
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(s2 == r3);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(s1));
            uint256_t const t3 = t2 | t1;
            bool const j10 = aot::nonzero(t3);
            if (j10) { MONAD_AOT_TAIL return b_1df5<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_37bf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_37bf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x1df5ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3614);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_37c6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x82, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x82, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            bool const j4 = aot::nonzero(s1);
            top[1] = uint256_t{0x0ull};
            top += 1;
            if (j4) { MONAD_AOT_TAIL return b_37d4<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_37cd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_37cd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x37d4ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x368a);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_37d4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x83, 0x14, 0x7f, 0x83, 0x14, 0x16, 0x15, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x83, 0x14, 0x7f, 0x83, 0x14, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(s2 == uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::from_bool(s1 == uint256_t{0x0ull, 0x0ull, 0x0ull, 0x8000000000000000ull});
            uint256_t const t3 = t2 & t1;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j10 = aot::nonzero(t4);
            if (j10) { MONAD_AOT_TAIL return b_3828<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3821<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3821(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x3828ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3614);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3828(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x05, 0x90, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x05, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t r2;
            runtime::sdiv(&r2, &s1, &s2);
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top[-3] = r2;
            top += -3;
            if (MONAD_LIKELY(jt < 14435)) {
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

    template void c_6d4316677b0cf491::run<EvmTraits<MONAD_ETH_OSAKA>>(
        void *, Context *, interpreter::Intercode const *, uint256_t *, void *);
}
