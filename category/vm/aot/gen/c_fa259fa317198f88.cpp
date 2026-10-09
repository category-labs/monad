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

// Written by aotgen.py from the code whose keccak is fa259fa317198f88f5fa3c119f06c066295dbcd47d715e0a30e1bcf94c02ef8c: not to be edited.

#include <category/vm/aot/ops.hpp>
#include <category/vm/interpreter/execute.hpp>
#include <category/vm/interpreter/intercode.hpp>

#define MONAD_AOT_TAIL __attribute__((musttail))

namespace monad::vm::aot
{
    using runtime::Context;
    using runtime::StatusCode;

    // 15623 bytes, keccak fa259fa317198f88f5fa3c119f06c066295dbcd47d715e0a30e1bcf94c02ef8c
    namespace c_fa259fa317198f88
    {
        template <Traits traits>
        using Block = void (*)(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        [[gnu::noinline]] void b_0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_12(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_25(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_30(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_46(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_51(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_5c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_67(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_72(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_7d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_88(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_93(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_bf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ca(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_eb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_101(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_117(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_122(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_12d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_138(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_143(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_157(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_181(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_202(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_249(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2fe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_398(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_39f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3d0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3e7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_409(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_417(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_41f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_459(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_461(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_49b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4a8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_4ac(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_4bb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_4be(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_4c7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4cc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4ec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_517(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_542(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_555(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_611(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_685(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_69a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6c1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6cf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6d5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6f9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_72a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_777(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_7d4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_8e6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ac0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ad4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b1b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b34(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_da7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e74(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e94(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ebe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_eda(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ee1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_ee9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f28(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f35(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f3e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f62(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f6c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_f71(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f8e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_f90(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fb1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fbf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fd8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_fe1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_101c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_105a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1070(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1082(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10c9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10e2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1115(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_113f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11ae(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11d7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_11ff(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1229(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_147c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14d1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_14f7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1516(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1541(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_157a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_15d8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_15ec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1686(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_16b3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_16ba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_16ef(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1734(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_185a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18cb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_18e4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_190f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1a68(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a6f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a9a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1aaf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1aba(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ac6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ad9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ae5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1af3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1aff(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1b2b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b33(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1b4f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b57(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1b5e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1b75(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1b83(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b8d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1bdb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c05(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c3e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c68(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1cb7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1cbe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ce8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d48(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d4f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d5a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1d94(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1da1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1daa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1dcd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1dd9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1de3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1de8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1e37(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1e39(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1e5e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1e6c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1e85(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1e8e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1eda(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f0e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1f4e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1fa1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fb0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fda(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2081(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2088(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2090(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_20d2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_20df(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_20e8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_210d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2115(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2121(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_212b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2130(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2156(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_215a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2163(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2194(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_21c5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_21e1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_222b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2249(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_225a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2262(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_226b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2289(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2292(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_22d8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_231c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2346(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2438(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2461(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_248a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_24b3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_24dc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_24e3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_250d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2575(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_259f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2697(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_26fe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2729(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2750(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_284b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2892(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_28c8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2950(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2a5d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2a7a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ac3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2b20(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b27(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b51(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2b5c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b97(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2bc1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2c5a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2c7c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2c9f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2cc2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2cc3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2cd3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2cd7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2cef(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2cf3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d0b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2d0f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d4c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2d50(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d7b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2d87(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2daa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2db8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2dc9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2dda(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2de8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2df5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e07(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e15(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2e16(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e42(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2e4a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e74(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e89(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2e94(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2e98(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ec4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2ecc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ef8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2f06(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2f41(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2f47(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2f8d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3016(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3023(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_304f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_30a9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_30f9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3106(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3132(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_313f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_316b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3177(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3178(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_319b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_319c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_31e8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_31f5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3221(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_322d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_322e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_324f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3250(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_325d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3289(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3296(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_32c2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_32cf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_32fb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3323(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3328(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3349(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_334c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_336e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_33a6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_33ad(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_33cf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3409(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_344d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3459(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_345f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_34b0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_34c7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_34e9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_34f0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_34f5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_34fb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3506(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3521(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3552(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_356b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_358a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3637(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3645(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_364f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3658(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3671(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_367c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_36cd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_370a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3710(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_371d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3720(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_372e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3738(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3741(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_376d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_37f8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3813(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_381d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3823(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3833(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_383b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_384d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_384e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3855(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3858(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3862(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_388f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_389b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_38a8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_38d4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_38db(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_38ec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3921(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_392d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3932(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_393e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3948(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_394a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3980(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_39da(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3a06(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3a15(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3a23(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3a52(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3a5f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3a6e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3a9d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3a9f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3ab2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3ab9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3aec(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3b37(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3b46(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3b54(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3b83(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3b90(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3b9f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3bce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3be1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3be8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3bf6(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c01(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3c0d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c1a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c27(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3c33(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c42(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c4d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3c55(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c63(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c70(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3c78(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3c85(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_3ccd(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        void bad(Context *const ctx, uint256_t const *, uint256_t *, int64_t)
        {
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        inline constexpr Block<traits> jump_table[15623] = {
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_12<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &b_249<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &b_398<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3d0<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_409<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_417<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_41f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_459<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_49b<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_4ac<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_4bb<traits>,
            &bad<traits>, &bad<traits>, &b_4be<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_4c7<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_7d4<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_8e6<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_ac0<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_eda<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_ee9<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_f28<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_f35<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_f3e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_f62<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_f6c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_f8e<traits>, &bad<traits>,
            &b_f90<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_fb1<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_fbf<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_fd8<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_fe1<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_101c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_105a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1070<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_15d8<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_15ec<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &b_1a68<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1ae5<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1af3<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1aff<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1b2b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1b4f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1b5e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1b75<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1b83<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &b_1cb7<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1d48<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1d5a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1d94<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1da1<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1daa<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1dcd<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1dd9<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1de3<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1e37<traits>, &bad<traits>, &b_1e39<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1e5e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1e6c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1e85<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1e8e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1eda<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1f0e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1f4e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1fa1<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2081<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2090<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_20d2<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_20df<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_20e8<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_210d<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2115<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2121<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_212b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2156<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_215a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2163<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_21c5<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_21e1<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_222b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2249<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_225a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2262<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_226b<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2289<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2292<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_22d8<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_24dc<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2697<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2b20<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2b5c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2c5a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2cc3<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_2cd7<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2cf3<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2d0f<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2d50<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_2d87<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2de8<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2e16<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2e4a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2e94<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2e98<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2ecc<traits>, &bad<traits>,
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
            &bad<traits>, &b_2f41<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3016<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3023<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_304f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_30a9<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_30f9<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3106<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3132<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_313f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_316b<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3178<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_319c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_31e8<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_31f5<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3221<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_322e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3250<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_325d<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_3289<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_3296<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_32c2<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_32cf<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_32fb<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3328<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_334c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_336e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_33a6<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_33cf<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_3409<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_344d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_345f<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_34b0<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_34c7<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_34e9<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_34f0<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_34f5<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_34fb<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_3506<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3521<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3552<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_356b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_358a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_3637<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3645<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_364f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3671<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_367c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_3710<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_371d<traits>, &bad<traits>, &bad<traits>,
            &b_3720<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_372e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3738<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_376d<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_37f8<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3813<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_381d<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_3823<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_383b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_384e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3858<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3862<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_389b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_38a8<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_38d4<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3921<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_392d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_3932<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_394a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_3980<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_39da<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3a06<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_3a15<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3a23<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_3a52<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3a5f<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3a6e<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3a9d<traits>,
            &bad<traits>, &b_3a9f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_3ab2<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3ab9<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3aec<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3b37<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3b46<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_3b54<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_3b83<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_3b90<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3b9f<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3bce<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3be1<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3be8<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_3c0d<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3c33<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_3c55<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_3c78<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_3c85<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_3ccd<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
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
            if (j8) { MONAD_AOT_TAIL return b_12<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_12(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x80, 0x35, 0x60, 0x1c, 0x80, 0x63, 0x14, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x80, 0x35, 0x60, 0x1c, 0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x0ull});
            uint256_t const t2 = aot::shr_c<224>(t1);
            uint256_t const t3 = aot::from_bool(uint256_t{0x13af4035ull} == t2);
            bool const j10 = aot::nonzero(t3);
            top[1] = uint256_t{0x0ull};
            top[2] = t2;
            top += 2;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2b90); }
            MONAD_AOT_TAIL return b_25<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_25(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x151c1adeull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_2b20<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_30<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_30(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x20b76e81ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x28c1); }
            MONAD_AOT_TAIL return b_3b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x238d6579ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x26f7); }
            MONAD_AOT_TAIL return b_46<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_46(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x2b4f013cull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x256e); }
            MONAD_AOT_TAIL return b_51<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_51(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x2c3c9157ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_24dc<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_5c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_5c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x3644e515ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2483); }
            MONAD_AOT_TAIL return b_67<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_67(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x46904840ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2431); }
            MONAD_AOT_TAIL return b_72<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_72(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x4d98a93bull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2315); }
            MONAD_AOT_TAIL return b_7d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_7d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x50d8cd4bull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_2081<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_88<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_88(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x5a64f51eull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1fa9); }
            MONAD_AOT_TAIL return b_93<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_93(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x5c2bea49ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_1d48<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_9e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x5c60e39aull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_1cb7<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_a9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x65e4ad9eull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1c37); }
            MONAD_AOT_TAIL return b_b4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x70ae92d2ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1bd4); }
            MONAD_AOT_TAIL return b_bf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_bf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x7784c685ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_1a68<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_ca<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ca(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x8069218full} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x167f); }
            MONAD_AOT_TAIL return b_d5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x8720316dull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x150f); }
            MONAD_AOT_TAIL return b_e0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x8c1358a2ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11f8); }
            MONAD_AOT_TAIL return b_eb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_eb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x8da5cb5bull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x11a7); }
            MONAD_AOT_TAIL return b_f6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x93c52062ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x110e); }
            MONAD_AOT_TAIL return b_101<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_101(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xa99aad89ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_eda<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_10c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xb485f3b8ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xe8d); }
            MONAD_AOT_TAIL return b_117<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_117(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xd8eabcb8ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x4e5); }
            MONAD_AOT_TAIL return b_122<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_122(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xe0232b42ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_398<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_12d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_12d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xe74b981bull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2cd); }
            MONAD_AOT_TAIL return b_138<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_138(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xeecea000ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1bb); }
            MONAD_AOT_TAIL return b_143<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_143(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x63, 0x14, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xf2b863ceull} == s0);
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x151); }
            MONAD_AOT_TAIL return b_14d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_157(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_181<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_181(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x60, 0x92, 0x73, 0x61, 0x61, 0x56}, 1, 6));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x60, 0x92, 0x73, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x20ull};
            top[1] = uint256_t{0xffull};
            top[2] = uint256_t{0x40ull};
            top[3] = m0;
            top[4] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[5] = uint256_t{0x1a4ull};
            top += 5;
            MONAD_AOT_TAIL return b_2c5a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x40ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_1ec<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x1f3ull};
            top += 1;
            MONAD_AOT_TAIL return b_2c5a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_202(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x33, 0x85, 0x52, 0x60, 0x60, 0x52, 0x73, 0x60, 0x86, 0x20, 0x94, 0x16, 0x93, 0x84, 0x60, 0x52, 0x60, 0x52, 0x61, 0x60, 0x60, 0x60, 0x20, 0x54, 0x16, 0x15, 0x15, 0x84, 0x14, 0x15, 0x61, 0x61, 0x56}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x33, 0x85, 0x52, 0x60, 0x60, 0x52, 0x73, 0x60, 0x86, 0x20, 0x94, 0x16, 0x93, 0x84, 0x60, 0x52, 0x60, 0x52, 0x61, 0x60, 0x60, 0x60, 0x20, 0x54, 0x16, 0x15, 0x15, 0x84, 0x14, 0x15, 0x61, 0x61, 0x56}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, t1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x6ull});
            uint256_t const t2 = aot::sha3_n<traits, 64>(ctx, gas, s3);
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = s2 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t2);
            uint256_t const t4 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t5 = aot::sload<traits>(ctx, gas, t4);
            uint256_t const t6 = t5 & uint256_t{0xffull};
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            uint256_t const &s1 = top[-1];
            uint256_t const t9 = aot::from_bool(s1 == t8);
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = t3;
            top[0] = uint256_t{0x297ull};
            top[1] = m0;
            top[2] = uint256_t{0x24full};
            top[3] = t10;
            top[4] = uint256_t{0x249ull};
            top += 4;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2fdd);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_249(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x61, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = m0;
            top[0] = m1;
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_2fe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2fe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x36cull};
            top[2] = uint256_t{0x308ull};
            top += 2;
            MONAD_AOT_TAIL return b_2c5a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_398(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j4 = aot::nonzero(t1);
            top += -1;
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_39f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_39f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x60ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_3c9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x3d0ull};
            top += 1;
            MONAD_AOT_TAIL return b_2c5a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3d0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x35, 0x82, 0x60, 0x35, 0x67, 0x81, 0x11, 0x61, 0x57}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x35, 0x82, 0x60, 0x35, 0x67, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t2);
            bool const j10 = aot::nonzero(t3);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = t1;
            top[2] = m1;
            top[3] = t2;
            top += 3;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x4e1); }
            MONAD_AOT_TAIL return b_3e7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3e7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x73, 0x91, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x73, 0x91, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[1] = uint256_t{0x409ull};
            top[2] = t1;
            top[3] = t2;
            top += 3;
            MONAD_AOT_TAIL return b_2de8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_409(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x90, 0x94, 0x61, 0x61, 0x61, 0x56}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x90, 0x94, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-5] = m1;
            top[-2] = m0;
            top[-1] = m2;
            top[0] = m5;
            top[1] = uint256_t{0x41full};
            top[2] = uint256_t{0x417ull};
            top += 2;
            MONAD_AOT_TAIL return b_32c2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_417(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x86, 0x15, 0x15, 0x61, 0x56}, 7, 2));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x86, 0x15, 0x15, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s6));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_41f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x16, 0x93, 0x84, 0x60, 0x51, 0x85, 0x81, 0x52, 0x7f, 0x60, 0x33, 0x92, 0xa3, 0x61, 0x84, 0x33, 0x87, 0x61, 0x56}, 6, 4));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x16, 0x93, 0x84, 0x60, 0x51, 0x85, 0x81, 0x52, 0x7f, 0x60, 0x33, 0x92, 0xa3, 0x61, 0x84, 0x33, 0x87, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 & s1;
            uint256_t const t2 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, t2, s4);
            uint256_t const t3 = runtime::uint256_from_address(ctx->env.sender);
            aot::log3<traits>(ctx, gas, t2, uint256_t{0x20ull}, uint256_t{0xf3bed7cb13fc4f12ull, 0x30e72651d37d3401ull, 0x7a9fa55a415d4ca4ull, 0xc76f1b4fe4396ac0ull}, t3, t1);
            gas = ctx->gas_remaining;
            uint256_t const t4 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const m4 = s4;
            top[-5] = t1;
            top[-1] = m5;
            top[0] = uint256_t{0x459ull};
            top[1] = m4;
            top[2] = t4;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_394a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_459(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x33, 0x3b, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x33, 0x3b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            ctx->gas_remaining = gas;
            uint256_t r2;
            runtime::extcodesize<traits>(ctx, &r2, &t1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::from_bool(!aot::nonzero(r2));
            bool const j5 = aot::nonzero(t2);
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x4d2); }
            MONAD_AOT_TAIL return b_461<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_461(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x91, 0x83, 0x91, 0x60, 0x51, 0x93, 0x84, 0x92, 0x83, 0x92, 0x7f, 0x84, 0x52, 0x88, 0x60, 0x85, 0x01, 0x61, 0x56}, 4, 8));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x91, 0x83, 0x91, 0x60, 0x51, 0x93, 0x84, 0x92, 0x83, 0x92, 0x7f, 0x84, 0x52, 0x88, 0x60, 0x85, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x31f5707200000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-1] = t1;
            top[0] = m2;
            top[1] = t1;
            top[2] = t1;
            top[3] = uint256_t{0x49bull};
            top[4] = m1;
            top[5] = m0;
            top[6] = m3;
            top[7] = t2;
            top += 7;
            MONAD_AOT_TAIL return b_319c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_49b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x03, 0x81, 0x83, 0x33, 0x5a, 0xf1, 0x80, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x03, 0x81, 0x83, 0x33, 0x5a, 0xf1, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t3 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xf1, 0x80, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const &s3 = top[-3];
            uint256_t const &s2 = top[-2];
            auto const c6 = aot::call<traits>(ctx, gas, t3, t2, s3, s2, t1, s2, s3, (aot::gas_of<traits>({0x80, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(c6));
            bool const j10 = aot::nonzero(t4);
            top[-3] = c6;
            top += -3;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x4d6); }
            MONAD_AOT_TAIL return b_4a8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4a8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j1 = aot::nonzero(s0);
            top += -1;
            if (j1) { MONAD_AOT_TAIL return b_4be<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_4ac<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_4ac(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x61, 0x91, 0x30, 0x90, 0x33, 0x90, 0x61, 0x56}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x61, 0x91, 0x30, 0x90, 0x33, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = uint256_t{0x4bbull};
            top[-1] = t1;
            top[0] = t2;
            top[1] = m3;
            top += 1;
            MONAD_AOT_TAIL return b_3ab9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_4bb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
        [[gnu::noinline]] void b_4be(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x90, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x4c7ull};
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_2cc3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_4c7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j2 = aot::nonzero(s0);
            top += -1;
            if (j2) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x4d2); }
            MONAD_AOT_TAIL return b_4cc<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4cc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x38, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x38, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[1] = m2;
            top[2] = uint256_t{0x3d07ull};
            top += 2;
            MONAD_AOT_TAIL return b_4ac<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4ec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x120ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_517<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_517(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x36, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x36, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            top[1] = uint256_t{0x51full};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_2d50<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_542(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x35, 0x67, 0x81, 0x11, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x35, 0x67, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x104ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j6 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x4e1); }
            MONAD_AOT_TAIL return b_555<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_555(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0x562ull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_2de8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_611(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x85, 0x91, 0x61, 0x57}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x85, 0x91, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            bool const j3 = aot::nonzero(s1);
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-1] = m5;
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xe50); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x617);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_685(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x67, 0x90, 0x80, 0x82, 0x02, 0x91, 0x82, 0x04, 0x03, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x67, 0x90, 0x80, 0x82, 0x02, 0x91, 0x82, 0x04, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(uint256_t{0x429d069189e0000ull}, s0);
            uint256_t const t2 = aot::udiv(t1, uint256_t{0x429d069189e0000ull});
            uint256_t const t3 = t2 - s0;
            bool const j10 = aot::nonzero(t3);
            top[0] = t1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_69a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_69a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x67, 0x90, 0x04, 0x91, 0x82, 0x67, 0x03, 0x92, 0x67, 0x84, 0x11, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x67, 0x90, 0x04, 0x91, 0x82, 0x67, 0x03, 0x92, 0x67, 0x84, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s0, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t2 = uint256_t{0xde0b6b3a7640000ull} - t1;
            uint256_t const t3 = aot::from_bool(uint256_t{0xde0b6b3a7640000ull} < t2);
            bool const j12 = aot::nonzero(t3);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t2;
            top[0] = m2;
            top[1] = t1;
            top += 1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xe23); }
            MONAD_AOT_TAIL return b_6c1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6c1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x67, 0x14, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x67, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xde0b6b3a7640000ull} == s0);
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xdf4); }
            MONAD_AOT_TAIL return b_6cf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6cf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x87, 0x15, 0x61, 0x57}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x87, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s7));
            bool const j3 = aot::nonzero(t1);
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xcfc); }
            MONAD_AOT_TAIL return b_6d5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6d5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x61, 0x90, 0x87, 0x61, 0x56}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x61, 0x90, 0x87, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[-1] = uint256_t{0x6dfull};
            top[0] = m1;
            top[1] = m7;
            top += 1;
            MONAD_AOT_TAIL return b_383b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6f9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x6e, 0x90, 0x04, 0x80, 0x67, 0x81, 0x02, 0x04, 0x67, 0x14, 0x81, 0x15, 0x17, 0x15, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x6e, 0x90, 0x04, 0x80, 0x67, 0x81, 0x02, 0x04, 0x67, 0x14, 0x81, 0x15, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::udiv(s0, uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull});
            uint256_t const t2 = aot::mul(t1, uint256_t{0xde0b6b3a7640000ull});
            uint256_t const t3 = aot::udiv(t2, t1);
            uint256_t const t4 = aot::from_bool(uint256_t{0xde0b6b3a7640000ull} == t3);
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t6 = t5 | t4;
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            bool const j15 = aot::nonzero(t7);
            top[0] = t1;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_72a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_72a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x67, 0x6e, 0x83, 0x90, 0x04, 0x80, 0x82, 0x18, 0x90, 0x82, 0x11, 0x02, 0x81, 0x18, 0x7f, 0x81, 0x01, 0x11, 0x61, 0x57}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x67, 0x6e, 0x83, 0x90, 0x04, 0x80, 0x82, 0x18, 0x90, 0x82, 0x11, 0x02, 0x81, 0x18, 0x7f, 0x81, 0x01, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::udiv(uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull}, s1);
            uint256_t const t2 = uint256_t{0xff59ee833b30000ull} ^ t1;
            uint256_t const t3 = aot::from_bool(t1 < uint256_t{0xff59ee833b30000ull});
            uint256_t const t4 = aot::mul(t3, t2);
            uint256_t const t5 = uint256_t{0xff59ee833b30000ull} ^ t4;
            uint256_t const t6 = t5 + uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t7 = aot::from_bool(t5 < t6);
            bool const j19 = aot::nonzero(t7);
            top[1] = uint256_t{0xff59ee833b30000ull};
            top += 1;
            if (j19) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xca0); }
            MONAD_AOT_TAIL return b_777<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_777(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x92, 0x61, 0x92, 0x6e, 0x91, 0x90, 0x91, 0x04, 0x80, 0x83, 0x18, 0x90, 0x83, 0x11, 0x02, 0x90, 0x91, 0x18, 0x90, 0x61, 0x90, 0x7f, 0x83, 0x01, 0x90, 0x67, 0x02, 0x61, 0x56}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x92, 0x61, 0x92, 0x6e, 0x91, 0x90, 0x91, 0x04, 0x80, 0x83, 0x18, 0x90, 0x83, 0x11, 0x02, 0x90, 0x91, 0x18, 0x90, 0x61, 0x90, 0x7f, 0x83, 0x01, 0x90, 0x67, 0x02, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::udiv(uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull}, s2);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 ^ t1;
            uint256_t const t3 = aot::from_bool(t1 < s0);
            uint256_t const t4 = aot::mul(t3, t2);
            uint256_t const t5 = s0 ^ t4;
            uint256_t const t6 = t5 + uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s1 = top[-1];
            uint256_t const t7 = aot::mul(uint256_t{0xde0b6b3a7640000ull}, s1);
            top[-2] = uint256_t{0x807ull};
            top[-1] = uint256_t{0x7d9ull};
            top[0] = t5;
            top[1] = uint256_t{0x7d4ull};
            top[2] = t6;
            top[3] = t7;
            top += 3;
            MONAD_AOT_TAIL return b_316b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_7d4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_384e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_8e6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x6f, 0x7f, 0x83, 0x54, 0x92, 0x60, 0x1b, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x56}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x6f, 0x7f, 0x83, 0x54, 0x92, 0x60, 0x1b, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::sload<traits>(ctx, gas, s1);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::shl_c<128>(s0);
            uint256_t const t3 = t2 & uint256_t{0x0ull, 0x0ull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t4 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t5 = t4 | t3;
            aot::sstore<traits>(ctx, gas, s1, t5, (aot::gas_of<traits>({0x56}) + 0));
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top += -3;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ac0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x51, 0x91, 0x82, 0x52, 0x60, 0x82, 0x01, 0x52, 0xf3}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x51, 0x91, 0x82, 0x52, 0x60, 0x82, 0x01, 0x52, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t1, s1);
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t2, s0);
            aot::finish(ctx, gas, StatusCode::Success, t1, s2);
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ad4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x91, 0x83, 0x91, 0x60, 0x51, 0x93, 0x84, 0x92, 0x83, 0x92, 0x7f, 0x84, 0x52, 0x88, 0x60, 0x85, 0x01, 0x61, 0x56}, 4, 8));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x91, 0x83, 0x91, 0x60, 0x51, 0x93, 0x84, 0x92, 0x83, 0x92, 0x7f, 0x84, 0x52, 0x88, 0x60, 0x85, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xcf7ea19600000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-1] = t1;
            top[0] = m2;
            top[1] = t1;
            top[2] = t1;
            top[3] = uint256_t{0xb0eull};
            top[4] = m1;
            top[5] = m0;
            top[6] = m3;
            top[7] = t2;
            top += 7;
            MONAD_AOT_TAIL return b_319c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b1b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j1 = aot::nonzero(s0);
            top += -1;
            if (j1) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xb25); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xb1f);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b34(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xb1f);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_da7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x6e, 0x61, 0x92, 0x02, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x6e, 0x61, 0x92, 0x02, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mul(s0, uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull});
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = uint256_t{0xdc1ull};
            top[0] = m1;
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_384e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e74(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x51, 0x38, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x51, 0x38, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            top[0] = t1;
            top[1] = uint256_t{0x3d07ull};
            top += 1;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x617);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e94(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_ebe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ebe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x60, 0x92, 0x60, 0x35, 0x81, 0x52, 0x60, 0x84, 0x52, 0x20, 0x54, 0x16, 0x60, 0x51, 0x90, 0x15, 0x15, 0x81, 0x52, 0xf3}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x60, 0x92, 0x60, 0x35, 0x81, 0x52, 0x60, 0x84, 0x52, 0x20, 0x54, 0x16, 0x60, 0x51, 0x90, 0x15, 0x15, 0x81, 0x52, 0xf3}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, t1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x5ull});
            uint256_t const t2 = aot::sha3_n<traits, 64>(ctx, gas, s0);
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const t4 = t3 & uint256_t{0xffull};
            uint256_t const t5 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            aot::mstore<traits>(ctx, gas, t5, t7);
            aot::finish(ctx, gas, StatusCode::Success, t5, uint256_t{0x20ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_eda(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j4 = aot::nonzero(t1);
            top += -1;
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_ee1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ee1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x36, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x36, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            top[1] = uint256_t{0xee9ull};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_2e16<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_ee9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x96, 0x91, 0x95, 0x92, 0x96, 0x95, 0x84, 0x60, 0x85, 0x20, 0x80, 0x85, 0x52, 0x60, 0x96, 0x60, 0x88, 0x52, 0x6f, 0x98, 0x61, 0x8a, 0x60, 0x60, 0x8a, 0x20, 0x01, 0x54, 0x16, 0x15, 0x15, 0x61, 0x61, 0x56}, 7, 10));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x96, 0x91, 0x95, 0x92, 0x96, 0x95, 0x84, 0x60, 0x85, 0x20, 0x80, 0x85, 0x52, 0x60, 0x96, 0x60, 0x88, 0x52, 0x6f, 0x98, 0x61, 0x8a, 0x60, 0x60, 0x8a, 0x20, 0x01, 0x54, 0x16, 0x15, 0x15, 0x61, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            auto const h11 = aot::sha3_any<traits>(ctx, gas, s5, uint256_t{0xa0ull});
            gas = ctx->gas_remaining;
            uint256_t const &s6 = top[-6];
            aot::mstore<traits>(ctx, gas, s6, h11);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s6);
            uint256_t const t2 = t1 + uint256_t{0x2ull};
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const m5 = s5;
            uint256_t const m6 = s6;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-6] = m2;
            top[-5] = m4;
            top[-4] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            top[-3] = uint256_t{0x20ull};
            top[-2] = m5;
            top[-1] = m6;
            top[1] = m1;
            top[2] = m3;
            top[3] = h11;
            top[4] = m3;
            top[5] = m4;
            top[6] = uint256_t{0xf28ull};
            top[7] = t6;
            top[8] = uint256_t{0x249ull};
            top += 8;
            MONAD_AOT_TAIL return b_3016<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f28(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x92, 0x61, 0x61, 0x61, 0x56}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x92, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = t1;
            top[0] = m3;
            top[1] = uint256_t{0xf3eull};
            top[2] = uint256_t{0xf35ull};
            top += 2;
            MONAD_AOT_TAIL return b_30f9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f35(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x15, 0x86, 0x18, 0x61, 0x56}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x15, 0x86, 0x18, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s2));
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = s5 ^ t1;
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f3e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x80, 0x9c, 0x16, 0x93, 0x61, 0x61, 0x61, 0x56}, 12, 4));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x80, 0x9c, 0x16, 0x93, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const t1 = s11 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-11] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[-3] = t1;
            top[1] = m3;
            top[2] = uint256_t{0xf62ull};
            top[3] = uint256_t{0x417ull};
            top += 3;
            MONAD_AOT_TAIL return b_3132<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f62(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x84, 0x8a, 0x61, 0x56}, 9, 4));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x84, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[1] = uint256_t{0xf6cull};
            top[2] = m3;
            top[3] = m8;
            top += 3;
            MONAD_AOT_TAIL return b_336e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f6c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j2 = aot::nonzero(s0);
            top += -1;
            if (j2) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x10e7); }
            MONAD_AOT_TAIL return b_f71<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_f71(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x80, 0x85, 0x52, 0x60, 0x87, 0x52, 0x61, 0x60, 0x86, 0x20, 0x54, 0x89, 0x81, 0x60, 0x1c, 0x91, 0x16, 0x8b, 0x61, 0x56}, 11, 3));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x80, 0x85, 0x52, 0x60, 0x87, 0x52, 0x61, 0x60, 0x86, 0x20, 0x54, 0x89, 0x81, 0x60, 0x1c, 0x91, 0x16, 0x8b, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s6, s2);
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, s8, uint256_t{0x3ull});
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s6);
            uint256_t const t2 = aot::sload<traits>(ctx, gas, t1);
            uint256_t const t3 = aot::shr_c<128>(t2);
            uint256_t const &s9 = top[-9];
            uint256_t const t4 = t2 & s9;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[-1] = uint256_t{0xf8eull};
            top[0] = t3;
            top[1] = t4;
            top[2] = m10;
            top += 2;
            MONAD_AOT_TAIL return b_3be8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f8e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x97}, 9, 0));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x97}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-8] = m0;
            top[0] = m8;
            MONAD_AOT_TAIL return b_f90<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_f90(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x86, 0x52, 0x60, 0x88, 0x52, 0x60, 0x86, 0x20, 0x83, 0x60, 0x52, 0x88, 0x52, 0x60, 0x60, 0x20, 0x61, 0x8a, 0x82, 0x54, 0x61, 0x56}, 9, 5));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x86, 0x52, 0x60, 0x88, 0x52, 0x60, 0x86, 0x20, 0x83, 0x60, 0x52, 0x88, 0x52, 0x60, 0x60, 0x20, 0x61, 0x8a, 0x82, 0x54, 0x61, 0x56}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s5, s1);
            uint256_t const &s7 = top[-7];
            aot::mstore<traits>(ctx, gas, s7, uint256_t{0x2ull});
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s5);
            uint256_t const &s2 = top[-2];
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, s2);
            aot::mstore<traits>(ctx, gas, s7, t1);
            uint256_t const t2 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[1] = t2;
            top[2] = uint256_t{0xfb1ull};
            top[3] = m8;
            top[4] = t3;
            top += 4;
            MONAD_AOT_TAIL return b_316b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fb1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x55, 0x61, 0x61, 0x8a, 0x61, 0x56}, 11, 2));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x55, 0x61, 0x61, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            aot::sstore<traits>(ctx, gas, s1, s0, (aot::gas_of<traits>({0x61, 0x61, 0x8a, 0x61, 0x56}) + 0));
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[-1] = uint256_t{0xfd8ull};
            top[0] = uint256_t{0xfbfull};
            top[1] = m10;
            top += 1;
            MONAD_AOT_TAIL return b_3c78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fbf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x88, 0x52, 0x60, 0x8a, 0x52, 0x61, 0x60, 0x89, 0x20, 0x91, 0x82, 0x54, 0x60, 0x1c, 0x61, 0x56}, 10, 4));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x88, 0x52, 0x60, 0x8a, 0x52, 0x61, 0x60, 0x89, 0x20, 0x91, 0x82, 0x54, 0x60, 0x1c, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s7, s3);
            uint256_t const &s9 = top[-9];
            aot::mstore<traits>(ctx, gas, s9, uint256_t{0x3ull});
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s7);
            uint256_t const t2 = aot::sload<traits>(ctx, gas, t1);
            uint256_t const t3 = aot::shr_c<128>(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = uint256_t{0x8e6ull};
            top[2] = m0;
            top[3] = t3;
            top += 3;
            MONAD_AOT_TAIL return b_3178<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fd8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x8a, 0x61, 0x56}, 10, 3));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[1] = uint256_t{0xfe1ull};
            top[2] = m9;
            top += 2;
            MONAD_AOT_TAIL return b_3c78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_fe1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x87, 0x52, 0x60, 0x89, 0x52, 0x7f, 0x60, 0x88, 0x20, 0x92, 0x61, 0x84, 0x54, 0x93, 0x82, 0x85, 0x16, 0x61, 0x56}, 9, 6));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x87, 0x52, 0x60, 0x89, 0x52, 0x7f, 0x60, 0x88, 0x20, 0x92, 0x61, 0x84, 0x54, 0x93, 0x82, 0x85, 0x16, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s6, s2);
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, s8, uint256_t{0x3ull});
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s6);
            uint256_t const t2 = aot::sload<traits>(ctx, gas, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = t2 & s1;
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = t1;
            top[0] = t2;
            top[1] = uint256_t{0x0ull, 0x0ull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            top[2] = m1;
            top[3] = uint256_t{0x101cull};
            top[4] = m0;
            top[5] = t3;
            top += 5;
            MONAD_AOT_TAIL return b_3178<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_101c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x60, 0x51, 0x90, 0x89, 0x82, 0x52, 0x88, 0x88, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x33, 0x93, 0xa4, 0x81, 0x61, 0x57}, 14, 0));
            if (MONAD_UNLIKELY(top - bottom < 14)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x60, 0x51, 0x90, 0x89, 0x82, 0x52, 0x88, 0x88, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x33, 0x93, 0xa4, 0x81, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 & s1;
            uint256_t const &s3 = top[-3];
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s3 & s2;
            uint256_t const t3 = t2 | t1;
            uint256_t const &s4 = top[-4];
            aot::sstore<traits>(ctx, gas, s4, t3, (aot::gas_of<traits>({0x60, 0x51, 0x90, 0x89, 0x82, 0x52, 0x88, 0x88, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x33, 0x93, 0xa4, 0x81, 0x61, 0x57}) + 0));
            uint256_t const t4 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s13 = top[-13];
            aot::mstore<traits>(ctx, gas, t4, s13);
            uint256_t const &s11 = top[-11];
            uint256_t const t5 = t4 + s11;
            uint256_t const &s12 = top[-12];
            aot::mstore<traits>(ctx, gas, t5, s12);
            uint256_t const t6 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const k22_1 = uint256_t{0x40ull};
            uint256_t const k22_2 = uint256_t{0xd75a3602cda30fe0ull, 0x8f12f6440918c20ull, 0xeb071d3df1caa8d0ull, 0xedf8870433c83823ull};
            uint256_t const &s5 = top[-5];
            uint256_t const &s6 = top[-6];
            ctx->gas_remaining = gas;
            runtime::log4<traits>(ctx, &t4, &k22_1, &k22_2, &s5, &t6, &s6);
            gas = ctx->gas_remaining;
            uint256_t const &s8 = top[-8];
            bool const j25 = aot::nonzero(s8);
            top += -7;
            if (j25) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x107a); }
            MONAD_AOT_TAIL return b_105a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_105a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x83, 0x60, 0x95, 0x61, 0x92, 0x51, 0x16, 0x30, 0x90, 0x33, 0x90, 0x61, 0x56}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x83, 0x60, 0x95, 0x61, 0x92, 0x51, 0x16, 0x30, 0x90, 0x33, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const &s7 = top[-7];
            uint256_t const t2 = t1 & s7;
            uint256_t const t3 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t4 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-7] = uint256_t{0x40ull};
            top[-3] = uint256_t{0x1070ull};
            top[-2] = m6;
            top[-1] = t3;
            top[0] = t4;
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_3ab9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1070(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x51, 0x92, 0x83, 0x52, 0x82, 0x01, 0x52, 0xf3}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x51, 0x92, 0x83, 0x52, 0x82, 0x01, 0x52, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t1, s2);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = t1 + s0;
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t2, s1);
            aot::finish(ctx, gas, StatusCode::Success, t1, s3);
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1082(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x91, 0x83, 0x91, 0x60, 0x51, 0x93, 0x84, 0x92, 0x83, 0x92, 0x7f, 0x84, 0x52, 0x8b, 0x60, 0x85, 0x01, 0x61, 0x56}, 7, 8));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x91, 0x83, 0x91, 0x60, 0x51, 0x93, 0x84, 0x92, 0x83, 0x92, 0x7f, 0x84, 0x52, 0x8b, 0x60, 0x85, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x2075be0300000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-1] = t1;
            top[0] = m2;
            top[1] = t1;
            top[2] = t1;
            top[3] = uint256_t{0x10bcull};
            top[4] = m1;
            top[5] = m0;
            top[6] = m6;
            top[7] = t2;
            top += 7;
            MONAD_AOT_TAIL return b_319c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10c9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j1 = aot::nonzero(s0);
            top += -1;
            if (j1) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x10d3); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x10cd);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10e2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x10cd);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1115(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x40ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_113f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_113f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x73, 0x60, 0x61, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x73, 0x60, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[2] = uint256_t{0x40ull};
            top[3] = uint256_t{0x115dull};
            top += 3;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2ca0);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11ae(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_11d7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11d7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x73, 0x60, 0x91, 0x54, 0x16, 0x60, 0x51, 0x90, 0x81, 0x52, 0xf3}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x73, 0x60, 0x91, 0x54, 0x16, 0x60, 0x51, 0x90, 0x81, 0x52, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::sload<traits>(ctx, gas, s0);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t3, t2);
            aot::finish(ctx, gas, StatusCode::Success, t3, uint256_t{0x20ull});
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_11ff(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0xa0ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_1229<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1229(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x36, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x36, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            top[1] = uint256_t{0x1231ull};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_2d50<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_147c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x84, 0x80, 0xf3}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x84, 0x80, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            aot::finish(ctx, gas, StatusCode::Success, s4, s4);
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14d1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j1 = aot::nonzero(s0);
            top += -1;
            if (j1) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x14db); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x14d5);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_14f7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x38, 0x80, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x38, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x3d07ull};
            top[2] = uint256_t{0x3d07ull};
            top += 2;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x14d5);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1516(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x100ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_1541<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1541(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x36, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x36, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            top[1] = uint256_t{0x1549ull};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_2d50<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_157a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x95, 0x87, 0x60, 0x93, 0x61, 0x61, 0x60, 0x86, 0x20, 0x92, 0x83, 0x85, 0x52, 0x60, 0x88, 0x52, 0x61, 0x6f, 0x60, 0x60, 0x88, 0x20, 0x01, 0x54, 0x16, 0x15, 0x15, 0x61, 0x61, 0x56}, 7, 11));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1013)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x95, 0x87, 0x60, 0x93, 0x61, 0x61, 0x60, 0x86, 0x20, 0x92, 0x83, 0x85, 0x52, 0x60, 0x88, 0x52, 0x61, 0x6f, 0x60, 0x60, 0x88, 0x20, 0x01, 0x54, 0x16, 0x15, 0x15, 0x61, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            auto const h9 = aot::sha3_any<traits>(ctx, gas, s0, uint256_t{0xa0ull});
            gas = ctx->gas_remaining;
            uint256_t const &s6 = top[-6];
            aot::mstore<traits>(ctx, gas, s6, h9);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s6);
            uint256_t const t2 = t1 + uint256_t{0x2ull};
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const m6 = s6;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-5] = uint256_t{0x4bbull};
            top[-1] = uint256_t{0x20ull};
            top[1] = m5;
            top[2] = m6;
            top[3] = h9;
            top[4] = uint256_t{0x1645ull};
            top[5] = uint256_t{0x163dull};
            top[6] = m1;
            top[7] = uint256_t{0x15baull};
            top[8] = t6;
            top[9] = uint256_t{0x249ull};
            top += 9;
            MONAD_AOT_TAIL return b_3016<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_15d8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x87, 0x15, 0x15, 0x61, 0x56}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x87, 0x15, 0x15, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s7));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_15ec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x249ull};
            top += 1;
            MONAD_AOT_TAIL return b_31e8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1686(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x36, 0x7f, 0x01, 0x81, 0x81, 0x12, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x36, 0x7f, 0x01, 0x81, 0x81, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x100ull}));
            bool const j8 = aot::nonzero(t3);
            top[1] = uint256_t{0x100ull};
            top[2] = t2;
            top += 2;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x4d2); }
            MONAD_AOT_TAIL return b_16b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_16b3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x13, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x13, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(slt(s0, uint256_t{0xa0ull}));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x4e1); }
            MONAD_AOT_TAIL return b_16ba<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_16ba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x61, 0x81, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            top[1] = t1;
            top[2] = uint256_t{0x16c5ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2cd7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_16ef(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x82, 0x01, 0x94, 0x85, 0x52, 0x60, 0x82, 0x01, 0x60, 0x35, 0x81, 0x52, 0x60, 0x35, 0x60, 0x84, 0x01, 0x90, 0x80, 0x82, 0x52, 0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 5, 6));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x82, 0x01, 0x94, 0x85, 0x52, 0x60, 0x82, 0x01, 0x60, 0x35, 0x81, 0x52, 0x60, 0x35, 0x60, 0x84, 0x01, 0x90, 0x80, 0x82, 0x52, 0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x40ull};
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, t1, s4);
            uint256_t const t2 = s1 + uint256_t{0x60ull};
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0x64ull});
            aot::mstore<traits>(ctx, gas, t2, t3);
            uint256_t const t4 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t5 = s1 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const t6 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t7 = t6 + uint256_t{0xffffffffffffff5cull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t8 = aot::from_bool(slt(t7, uint256_t{0x60ull}));
            bool const j28 = aot::nonzero(t8);
            top[-4] = t1;
            top[1] = t2;
            top[2] = t5;
            top[3] = t4;
            top += 3;
            if (j28) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a64); }
            MONAD_AOT_TAIL return b_1734<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1734(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x61, 0x91, 0x61, 0x82, 0x61, 0x56}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x61, 0x91, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x1774ull};
            top[1] = t1;
            top[2] = m0;
            top[3] = uint256_t{0x1743ull};
            top[4] = t1;
            top += 4;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_185a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x83, 0x60, 0x52, 0x84, 0x51, 0x90, 0x20, 0x90, 0x84, 0x01, 0x90, 0x7f, 0x82, 0x52, 0x7f, 0x61, 0x86, 0x01, 0x52, 0x61, 0x85, 0x01, 0x52, 0x60, 0x83, 0x52, 0x61, 0x84, 0x01, 0x91, 0x83, 0x83, 0x10, 0x90, 0x83, 0x11, 0x17, 0x61, 0x57}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x83, 0x60, 0x52, 0x84, 0x51, 0x90, 0x20, 0x90, 0x84, 0x01, 0x90, 0x7f, 0x82, 0x52, 0x7f, 0x61, 0x86, 0x01, 0x52, 0x61, 0x85, 0x01, 0x52, 0x60, 0x83, 0x52, 0x61, 0x84, 0x01, 0x91, 0x83, 0x83, 0x10, 0x90, 0x83, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s4);
            uint256_t const &s0 = top[0];
            auto const h6 = aot::sha3_any<traits>(ctx, gas, s0, t1);
            gas = ctx->gas_remaining;
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s4 + s1;
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x1901000000000000ull});
            uint256_t const t3 = s4 + uint256_t{0x102ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0x1e0eb9f28cafdd2dull, 0xc7a4a17b4db99be4ull, 0x12b671d38548b711ull, 0xec6ac4ec64693757ull});
            uint256_t const t4 = s4 + uint256_t{0x122ull};
            aot::mstore<traits>(ctx, gas, t4, h6);
            aot::mstore<traits>(ctx, gas, s3, uint256_t{0x42ull});
            uint256_t const t5 = s4 + uint256_t{0x160ull};
            uint256_t const t6 = aot::from_bool(t5 < s3);
            uint256_t const &s2 = top[-2];
            uint256_t const t7 = aot::from_bool(s2 < t5);
            uint256_t const t8 = t7 | t6;
            bool const j38 = aot::nonzero(t8);
            top[-2] = t5;
            top[-1] = t2;
            top += -1;
            if (j38) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a35); }
            MONAD_AOT_TAIL return b_18cb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18cb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x8a, 0x92, 0x82, 0x60, 0x52, 0x51, 0x90, 0x20, 0x90, 0x60, 0x35, 0x93, 0x60, 0x85, 0x16, 0x80, 0x95, 0x03, 0x61, 0x57}, 11, 3));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x8a, 0x92, 0x82, 0x60, 0x52, 0x51, 0x90, 0x20, 0x90, 0x60, 0x35, 0x93, 0x60, 0x85, 0x16, 0x80, 0x95, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, s1);
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const &s0 = top[0];
            auto const h7 = aot::sha3_any<traits>(ctx, gas, s0, t1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const t3 = t2 & uint256_t{0xffull};
            uint256_t const t4 = t2 - t3;
            bool const j19 = aot::nonzero(t4);
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const m1 = s1;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = t3;
            top[-2] = m10;
            top[-1] = h7;
            top[0] = m1;
            top[1] = m3;
            top += 1;
            if (j19) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a31); }
            MONAD_AOT_TAIL return b_18e4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_18e4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x88, 0x94, 0x60, 0x93, 0x83, 0x52, 0x61, 0x82, 0x01, 0x52, 0x60, 0x35, 0x61, 0x82, 0x01, 0x52, 0x61, 0x60, 0x35, 0x91, 0x01, 0x52, 0x82, 0x80, 0x52, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 9, 3));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x88, 0x94, 0x60, 0x93, 0x83, 0x52, 0x61, 0x82, 0x01, 0x52, 0x60, 0x35, 0x61, 0x82, 0x01, 0x52, 0x61, 0x60, 0x35, 0x91, 0x01, 0x52, 0x82, 0x80, 0x52, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s1, s2);
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x180ull};
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, t1, s4);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0xc4ull});
            uint256_t const t3 = s0 + uint256_t{0x1a0ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = aot::calldataload(ctx, uint256_t{0xe4ull});
            uint256_t const t5 = s0 + uint256_t{0x1c0ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, s3);
            uint256_t const t6 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k27_1 = uint256_t{0x1ull};
            uint256_t const k27_3 = uint256_t{0x80ull};
            uint256_t const &s8 = top[-8];
            ctx->gas_remaining = gas;
            uint256_t r27;
            runtime::staticcall<traits>(ctx, &r27, &t6, &k27_1, &s1, &k27_3, &s3, &s8, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t7 = aot::from_bool(!aot::nonzero(r27));
            bool const j30 = aot::nonzero(t7);
            top += -5;
            if (j30) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a26); }
            MONAD_AOT_TAIL return b_190f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_190f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x92, 0x82, 0x91, 0x61, 0x83, 0x8a, 0x51, 0x16, 0x80, 0x15, 0x15, 0x90, 0x81, 0x61, 0x57}, 7, 7));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x92, 0x82, 0x91, 0x61, 0x83, 0x8a, 0x51, 0x16, 0x80, 0x15, 0x15, 0x90, 0x81, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s6);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 & s1;
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j15 = aot::nonzero(t4);
            uint256_t const m1 = s1;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = uint256_t{0x2bf132d0326309c0ull, 0x5e3f237311f5648ull, 0x3f766bdebad25f0aull, 0xd5e969f01efe921dull};
            top[0] = m1;
            top[1] = m2;
            top[2] = m0;
            top[3] = uint256_t{0x197full};
            top[4] = t4;
            top[5] = t2;
            top += 5;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a19); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1943);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1a68(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j4 = aot::nonzero(t1);
            top += -1;
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_1a6f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a6f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x4e1); }
            MONAD_AOT_TAIL return b_1a9a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a9a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x90, 0x67, 0x90, 0x81, 0x83, 0x11, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x90, 0x67, 0x90, 0x81, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = uint256_t{0xffffffffffffffffull};
            top[2] = m0;
            top += 2;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a31); }
            MONAD_AOT_TAIL return b_1aaf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1aaf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a31); }
            MONAD_AOT_TAIL return b_1aba<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1aba(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a31); }
            MONAD_AOT_TAIL return b_1ac6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ac6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x91, 0x60, 0x90, 0x36, 0x84, 0x82, 0x84, 0x1b, 0x87, 0x01, 0x01, 0x11, 0x61, 0x57}, 3, 6));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x91, 0x60, 0x90, 0x36, 0x84, 0x82, 0x84, 0x1b, 0x87, 0x01, 0x01, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::shl_c<5>(s1);
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = s2 + t2;
            uint256_t const t4 = t3 + uint256_t{0x24ull};
            uint256_t const t5 = aot::from_bool(t1 < t4);
            bool const j14 = aot::nonzero(t5);
            uint256_t const m1 = s1;
            top[-1] = uint256_t{0x24ull};
            top[1] = uint256_t{0x5ull};
            top[2] = m1;
            top += 2;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1bd0); }
            MONAD_AOT_TAIL return b_1ad9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ad9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x84, 0x91, 0x81, 0x61, 0x88, 0x93, 0x61, 0x56}, 6, 5));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x84, 0x91, 0x81, 0x61, 0x88, 0x93, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = m4;
            top[0] = m5;
            top[1] = m1;
            top[2] = m0;
            top[3] = uint256_t{0x1ae5ull};
            top[4] = m0;
            top += 4;
            MONAD_AOT_TAIL return b_3823<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ae5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x95, 0x61, 0x60, 0x51, 0x97, 0x88, 0x61, 0x56}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x95, 0x61, 0x60, 0x51, 0x97, 0x88, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-6] = t1;
            top[0] = m6;
            top[1] = uint256_t{0x1af3ull};
            top[2] = m0;
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2d0f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1af3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x87, 0x52, 0x61, 0x82, 0x61, 0x56}, 7, 3));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x87, 0x52, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s6, s1);
            uint256_t const m1 = s1;
            top[1] = uint256_t{0x1affull};
            top[2] = m1;
            top += 2;
            MONAD_AOT_TAIL return b_3823<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1aff(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x94, 0x7f, 0x87, 0x89, 0x01, 0x96, 0x01, 0x36, 0x87, 0x37, 0x84}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x94, 0x7f, 0x87, 0x89, 0x01, 0x96, 0x01, 0x36, 0x87, 0x37, 0x84}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s7 + s6;
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 + uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t1, &t3, &t2);
            gas = ctx->gas_remaining;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-5] = t1;
            top[0] = m5;
            top[1] = m4;
            top += 1;
            MONAD_AOT_TAIL return b_1b2b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1b2b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j5) { MONAD_AOT_TAIL return b_1b75<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1b33<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b33(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x60, 0x51, 0x93, 0x83, 0x85, 0x94, 0x85, 0x01, 0x91, 0x81, 0x86, 0x52, 0x51, 0x80, 0x92, 0x52, 0x60, 0x85, 0x01, 0x93, 0x92}, 9, 0));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x60, 0x51, 0x93, 0x83, 0x85, 0x94, 0x85, 0x01, 0x91, 0x81, 0x86, 0x52, 0x51, 0x80, 0x92, 0x52, 0x60, 0x85, 0x01, 0x93, 0x92}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s7 = top[-7];
            uint256_t const t2 = t1 + s7;
            aot::mstore<traits>(ctx, gas, t1, s7);
            uint256_t const &s8 = top[-8];
            uint256_t const t3 = aot::mload<traits>(ctx, gas, s8);
            aot::mstore<traits>(ctx, gas, t2, t3);
            uint256_t const t4 = t1 + uint256_t{0x40ull};
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const m7 = s7;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-8] = t1;
            top[-7] = t1;
            top[-6] = t4;
            top[-5] = m6;
            top[-4] = t3;
            top[-3] = m7;
            top[-2] = m5;
            top += -2;
            MONAD_AOT_TAIL return b_1b4f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1b4f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j5) { MONAD_AOT_TAIL return b_1b5e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1b57<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b57(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x03, 0x90, 0xf3}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x03, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = s4 - s5;
            uint256_t const &s6 = top[-6];
            aot::finish(ctx, gas, StatusCode::Success, s6, t1);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1b5e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x51, 0x85, 0x52, 0x86, 0x95, 0x50, 0x93, 0x81, 0x01, 0x93, 0x92, 0x81, 0x01, 0x92, 0x60, 0x01, 0x61, 0x56}, 7, 2));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x51, 0x85, 0x52, 0x86, 0x95, 0x50, 0x93, 0x81, 0x01, 0x93, 0x92, 0x81, 0x01, 0x92, 0x60, 0x01, 0x61, 0x56}) + 0;
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
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-5] = m6;
            top[-4] = t2;
            top[-3] = t3;
            top[0] = t4;
            MONAD_AOT_TAIL return b_1b4f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1b75(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x94, 0x97, 0x95, 0x96, 0x94, 0x61, 0x81, 0x61, 0x56}, 9, 3));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x94, 0x97, 0x95, 0x96, 0x94, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-8] = m5;
            top[-7] = m6;
            top[-6] = m8;
            top[-5] = m7;
            top[1] = uint256_t{0x1b83ull};
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_32fb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1b83(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x84, 0x81, 0x10, 0x15, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x84, 0x81, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::from_bool(s1 < s4);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m1 = s1;
            top[-1] = m0;
            top[0] = m1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1ba4); }
            MONAD_AOT_TAIL return b_1b8d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1b8d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x85, 0x1b, 0x82, 0x01, 0x83, 0x01, 0x35, 0x54, 0x81, 0x86, 0x1b, 0x88, 0x01, 0x52, 0x95, 0x97, 0x94, 0x96, 0x95, 0x61, 0x56}, 10, 2));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x85, 0x1b, 0x82, 0x01, 0x83, 0x01, 0x35, 0x54, 0x81, 0x86, 0x1b, 0x88, 0x01, 0x52, 0x95, 0x97, 0x94, 0x96, 0x95, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl(s5, s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s2 + t1;
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = s3 + t2;
            uint256_t const t4 = aot::calldataload(ctx, t3);
            uint256_t const t5 = aot::sload<traits>(ctx, gas, t4);
            uint256_t const &s1 = top[-1];
            uint256_t const t6 = aot::shl(s5, s1);
            uint256_t const &s7 = top[-7];
            uint256_t const t7 = s7 + t6;
            aot::mstore<traits>(ctx, gas, t7, t5);
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[-9] = m7;
            top[-8] = m6;
            top[-7] = m8;
            top[-6] = m9;
            top += -1;
            MONAD_AOT_TAIL return b_1b2b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1bdb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_1c05<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c05(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x91, 0x73, 0x61, 0x61, 0x56}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x91, 0x73, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x20ull};
            top[1] = uint256_t{0x40ull};
            top[2] = m0;
            top[3] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[4] = uint256_t{0x1c26ull};
            top += 4;
            MONAD_AOT_TAIL return b_2c5a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c3e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x40ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_1c68<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c68(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x1c6full};
            top += 1;
            MONAD_AOT_TAIL return b_2c5a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1cb7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j4 = aot::nonzero(t1);
            top += -1;
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_1cbe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1cbe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_1ce8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ce8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x91, 0x60, 0x35, 0x81, 0x52, 0x60, 0x60, 0x52, 0x20, 0x80, 0x54, 0x60, 0x60, 0x83, 0x01, 0x54, 0x92, 0x01, 0x54, 0x90, 0x60, 0x51, 0x92, 0x6f, 0x91, 0x82, 0x81, 0x16, 0x85, 0x52, 0x60, 0x1c, 0x60, 0x85, 0x01, 0x52, 0x81, 0x81, 0x16, 0x60, 0x85, 0x01, 0x52, 0x60, 0x1c, 0x60, 0x84, 0x01, 0x52, 0x81, 0x16, 0x60, 0x83, 0x01, 0x52, 0x60, 0x1c, 0x60, 0x82, 0x01, 0x52, 0xf3}, 1, 7));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x91, 0x60, 0x35, 0x81, 0x52, 0x60, 0x60, 0x52, 0x20, 0x80, 0x54, 0x60, 0x60, 0x83, 0x01, 0x54, 0x92, 0x01, 0x54, 0x90, 0x60, 0x51, 0x92, 0x6f, 0x91, 0x82, 0x81, 0x16, 0x85, 0x52, 0x60, 0x1c, 0x60, 0x85, 0x01, 0x52, 0x81, 0x81, 0x16, 0x60, 0x85, 0x01, 0x52, 0x60, 0x1c, 0x60, 0x84, 0x01, 0x52, 0x81, 0x16, 0x60, 0x83, 0x01, 0x52, 0x60, 0x1c, 0x60, 0x82, 0x01, 0x52, 0xf3}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, t1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const t2 = aot::sha3_n<traits, 64>(ctx, gas, s0);
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const t4 = t2 + uint256_t{0x1ull};
            uint256_t const t5 = aot::sload<traits>(ctx, gas, t4);
            uint256_t const t6 = t2 + uint256_t{0x2ull};
            uint256_t const t7 = aot::sload<traits>(ctx, gas, t6);
            uint256_t const t8 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t9 = t3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            aot::mstore<traits>(ctx, gas, t8, t9);
            uint256_t const t10 = aot::shr_c<128>(t3);
            uint256_t const t11 = t8 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t11, t10);
            uint256_t const t12 = t5 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t13 = t8 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t13, t12);
            uint256_t const t14 = aot::shr_c<128>(t5);
            uint256_t const t15 = t8 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t15, t14);
            uint256_t const t16 = t7 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t17 = t8 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t17, t16);
            uint256_t const t18 = aot::shr_c<128>(t7);
            uint256_t const t19 = t8 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t19, t18);
            aot::finish(ctx, gas, StatusCode::Success, t8, uint256_t{0xc0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d48(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j4 = aot::nonzero(t1);
            top += -1;
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_1d4f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1d4f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x90, 0x61, 0x36, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x90, 0x61, 0x36, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x40ull};
            top[1] = m0;
            top[2] = uint256_t{0x1d5aull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2e98<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d5a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x94, 0x93, 0x91, 0x90, 0x85, 0x82, 0x60, 0x85, 0x20, 0x91, 0x82, 0x88, 0x52, 0x60, 0x60, 0x52, 0x61, 0x6f, 0x60, 0x8c, 0x8b, 0x20, 0x01, 0x54, 0x16, 0x15, 0x15, 0x61, 0x61, 0x56}, 7, 8));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x94, 0x93, 0x91, 0x90, 0x85, 0x82, 0x60, 0x85, 0x20, 0x91, 0x82, 0x88, 0x52, 0x60, 0x60, 0x52, 0x61, 0x6f, 0x60, 0x8c, 0x8b, 0x20, 0x01, 0x54, 0x16, 0x15, 0x15, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            auto const h10 = aot::sha3_any<traits>(ctx, gas, s4, uint256_t{0xa0ull});
            gas = ctx->gas_remaining;
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, s5, h10);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const &s6 = top[-6];
            auto const h23 = aot::sha3_any<traits>(ctx, gas, s5, s6);
            gas = ctx->gas_remaining;
            uint256_t const t1 = h23 + uint256_t{0x2ull};
            uint256_t const t2 = aot::sload<traits>(ctx, gas, t1);
            uint256_t const t3 = t2 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const m5 = s5;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m4 = s4;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-5] = m3;
            top[-4] = m5;
            top[-3] = m0;
            top[-2] = m4;
            top[-1] = m2;
            top[0] = m1;
            top[1] = h10;
            top[2] = m2;
            top[3] = m3;
            top[4] = uint256_t{0x1d94ull};
            top[5] = t5;
            top[6] = uint256_t{0x249ull};
            top += 6;
            MONAD_AOT_TAIL return b_3016<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1d94(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x93, 0x61, 0x61, 0x61, 0x56}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x93, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-4] = t1;
            top[0] = m4;
            top[1] = uint256_t{0x1daaull};
            top[2] = uint256_t{0x1da1ull};
            top += 2;
            MONAD_AOT_TAIL return b_30f9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1da1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x15, 0x87, 0x18, 0x61, 0x56}, 7, 2));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x15, 0x87, 0x18, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s2));
            uint256_t const &s6 = top[-6];
            uint256_t const t2 = s6 ^ t1;
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1daa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x87, 0x16, 0x94, 0x61, 0x61, 0x61, 0x56}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x87, 0x16, 0x94, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s6 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-4] = t1;
            top[1] = m4;
            top[2] = uint256_t{0x1dcdull};
            top[3] = uint256_t{0x15d8ull};
            top += 3;
            MONAD_AOT_TAIL return b_3132<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1dcd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x86, 0x61, 0x56}, 5, 4));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x86, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[1] = uint256_t{0x1dd9ull};
            top[2] = uint256_t{0x15ecull};
            top[3] = m4;
            top += 3;
            MONAD_AOT_TAIL return b_3328<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1dd9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x84, 0x88, 0x61, 0x56}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x84, 0x88, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[1] = uint256_t{0x1de3ull};
            top[2] = m3;
            top[3] = m6;
            top += 3;
            MONAD_AOT_TAIL return b_336e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1de3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j2 = aot::nonzero(s0);
            top += -1;
            if (j2) { MONAD_AOT_TAIL return b_1f4e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1de8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1de8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x92, 0x61, 0x94, 0x92, 0x73, 0x92, 0x85, 0x89, 0x96, 0x89, 0x52, 0x60, 0x60, 0x52, 0x61, 0x8b, 0x61, 0x81, 0x8c, 0x20, 0x54, 0x6f, 0x81, 0x60, 0x1c, 0x91, 0x16, 0x8b, 0x61, 0x56}, 10, 8));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x92, 0x61, 0x94, 0x92, 0x73, 0x92, 0x85, 0x89, 0x96, 0x89, 0x52, 0x60, 0x60, 0x52, 0x61, 0x8b, 0x61, 0x81, 0x8c, 0x20, 0x54, 0x6f, 0x81, 0x60, 0x1c, 0x91, 0x16, 0x8b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s7, s2);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const &s9 = top[-9];
            auto const h21 = aot::sha3_any<traits>(ctx, gas, s7, s9);
            gas = ctx->gas_remaining;
            uint256_t const t1 = aot::sload<traits>(ctx, gas, h21);
            uint256_t const t2 = aot::shr_c<128>(t1);
            uint256_t const t3 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const m2 = s2;
            uint256_t const m9 = s9;
            top[-6] = uint256_t{0xac0ull};
            top[-5] = m8;
            top[-4] = m6;
            top[-3] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[-2] = m5;
            top[-1] = m4;
            top[0] = m3;
            top[1] = m2;
            top[2] = uint256_t{0x1f0eull};
            top[3] = m9;
            top[4] = uint256_t{0x1e37ull};
            top[5] = t2;
            top[6] = t3;
            top[7] = m8;
            top += 7;
            MONAD_AOT_TAIL return b_3c33<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1e37(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x9a}, 12, 0));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x9a}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            top[-11] = m0;
            top[0] = m11;
            MONAD_AOT_TAIL return b_1e39<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1e39(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x81, 0x52, 0x60, 0x60, 0x52, 0x87, 0x82, 0x82, 0x20, 0x95, 0x16, 0x94, 0x85, 0x60, 0x52, 0x60, 0x52, 0x81, 0x60, 0x20, 0x61, 0x8d, 0x82, 0x54, 0x61, 0x56}, 12, 5));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x81, 0x52, 0x60, 0x60, 0x52, 0x87, 0x82, 0x82, 0x20, 0x95, 0x16, 0x94, 0x85, 0x60, 0x52, 0x60, 0x52, 0x81, 0x60, 0x20, 0x61, 0x8d, 0x82, 0x54, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s0, s3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x2ull});
            uint256_t const &s1 = top[-1];
            auto const h10 = aot::sha3_any<traits>(ctx, gas, s0, s1);
            gas = ctx->gas_remaining;
            uint256_t const &s4 = top[-4];
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = s4 & s7;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, h10);
            auto const h21 = aot::sha3_any<traits>(ctx, gas, uint256_t{0x0ull}, s1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::sload<traits>(ctx, gas, h21);
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            top[-4] = t1;
            top[1] = h21;
            top[2] = uint256_t{0x1e5eull};
            top[3] = m11;
            top[4] = t2;
            top += 4;
            MONAD_AOT_TAIL return b_3221<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1e5e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x55, 0x61, 0x61, 0x8d, 0x61, 0x56}, 14, 2));
            if (MONAD_UNLIKELY(top - bottom < 14)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x55, 0x61, 0x61, 0x8d, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            aot::sstore<traits>(ctx, gas, s1, s0, (aot::gas_of<traits>({0x61, 0x61, 0x8d, 0x61, 0x56}) + 0));
            uint256_t const &s13 = top[-13];
            uint256_t const m13 = s13;
            top[-1] = uint256_t{0x1e85ull};
            top[0] = uint256_t{0x1e6cull};
            top[1] = m13;
            top += 1;
            MONAD_AOT_TAIL return b_3c78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1e6c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x85, 0x83, 0x52, 0x60, 0x60, 0x52, 0x61, 0x84, 0x84, 0x20, 0x91, 0x82, 0x54, 0x60, 0x1c, 0x61, 0x56}, 6, 4));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x85, 0x83, 0x52, 0x60, 0x60, 0x52, 0x61, 0x84, 0x84, 0x20, 0x91, 0x82, 0x54, 0x60, 0x1c, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, s2, s5);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const &s3 = top[-3];
            auto const h10 = aot::sha3_any<traits>(ctx, gas, s2, s3);
            gas = ctx->gas_remaining;
            uint256_t const t1 = aot::sload<traits>(ctx, gas, h10);
            uint256_t const t2 = aot::shr_c<128>(t1);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = h10;
            top[1] = uint256_t{0x8e6ull};
            top[2] = m0;
            top[3] = t2;
            top += 3;
            MONAD_AOT_TAIL return b_322e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1e85(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x8a, 0x61, 0x56}, 10, 3));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[1] = uint256_t{0x1e8eull};
            top[2] = m9;
            top += 2;
            MONAD_AOT_TAIL return b_3c78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1e8e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x82, 0x52, 0x60, 0x60, 0x52, 0x82, 0x82, 0x20, 0x90, 0x7f, 0x6f, 0x61, 0x84, 0x54, 0x93, 0x82, 0x85, 0x16, 0x61, 0x56}, 5, 7));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x82, 0x52, 0x60, 0x60, 0x52, 0x82, 0x82, 0x20, 0x90, 0x7f, 0x6f, 0x61, 0x84, 0x54, 0x93, 0x82, 0x85, 0x16, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, s1, s4);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const &s2 = top[-2];
            auto const h9 = aot::sha3_any<traits>(ctx, gas, s1, s2);
            gas = ctx->gas_remaining;
            uint256_t const t1 = aot::sload<traits>(ctx, gas, h9);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = h9;
            top[1] = t1;
            top[2] = uint256_t{0x0ull, 0x0ull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            top[3] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            top[4] = uint256_t{0x1edaull};
            top[5] = m0;
            top[6] = t2;
            top += 6;
            MONAD_AOT_TAIL return b_322e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1eda(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x83, 0x81, 0x52, 0x60, 0x60, 0x52, 0x20, 0x6f, 0x80, 0x60, 0x83, 0x01, 0x54, 0x16, 0x91, 0x54, 0x16, 0x10, 0x15, 0x61, 0x61, 0x56}, 9, 0));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x83, 0x81, 0x52, 0x60, 0x60, 0x52, 0x20, 0x6f, 0x80, 0x60, 0x83, 0x01, 0x54, 0x16, 0x91, 0x54, 0x16, 0x10, 0x15, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 & s1;
            uint256_t const &s3 = top[-3];
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s3 & s2;
            uint256_t const t3 = t2 | t1;
            uint256_t const &s4 = top[-4];
            aot::sstore<traits>(ctx, gas, s4, t3, (aot::gas_of<traits>({0x83, 0x81, 0x52, 0x60, 0x60, 0x52, 0x20, 0x6f, 0x80, 0x60, 0x83, 0x01, 0x54, 0x16, 0x91, 0x54, 0x16, 0x10, 0x15, 0x61, 0x61, 0x56}) + 0));
            uint256_t const &s5 = top[-5];
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, s5, s8);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const &s6 = top[-6];
            auto const h13 = aot::sha3_any<traits>(ctx, gas, s5, s6);
            gas = ctx->gas_remaining;
            uint256_t const t4 = h13 + uint256_t{0x1ull};
            uint256_t const t5 = aot::sload<traits>(ctx, gas, t4);
            uint256_t const t6 = t5 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t7 = aot::sload<traits>(ctx, gas, h13);
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t9 = aot::from_bool(t8 < t6);
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            top[-6] = t10;
            top[-5] = uint256_t{0x249ull};
            top += -5;
            MONAD_AOT_TAIL return b_3250<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f0e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x8a, 0x51, 0x33, 0x81, 0x52, 0x60, 0x81, 0x01, 0x88, 0x90, 0x52, 0x60, 0x81, 0x01, 0x8a, 0x90, 0x52, 0x7f, 0x90, 0x60, 0x90, 0xa4, 0x51, 0x16, 0x61, 0x56}, 11, 3));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x8a, 0x51, 0x33, 0x81, 0x52, 0x60, 0x81, 0x01, 0x88, 0x90, 0x52, 0x60, 0x81, 0x01, 0x8a, 0x90, 0x52, 0x7f, 0x90, 0x60, 0x90, 0xa4, 0x51, 0x16, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s10 = top[-10];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s10);
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.sender);
            aot::mstore<traits>(ctx, gas, t1, t2);
            uint256_t const t3 = t1 + uint256_t{0x20ull};
            uint256_t const &s6 = top[-6];
            aot::mstore<traits>(ctx, gas, t3, s6);
            uint256_t const t4 = t1 + uint256_t{0x40ull};
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, t4, s8);
            uint256_t const k22_1 = uint256_t{0x60ull};
            uint256_t const k22_2 = uint256_t{0x75fc6484cf58fbfull, 0x62437c32db1aa1aaull, 0xce63666221f796fbull, 0xa56fc0ad5702ec05ull};
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            ctx->gas_remaining = gas;
            runtime::log4<traits>(ctx, &t1, &k22_1, &k22_2, &s0, &s1, &s2);
            gas = ctx->gas_remaining;
            uint256_t const &s3 = top[-3];
            uint256_t const t5 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t6 = t5 & s4;
            top[-4] = t6;
            top += -4;
            MONAD_AOT_TAIL return b_394a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1f4e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x89, 0x98, 0x50, 0x92, 0x82, 0x61, 0x61, 0x73, 0x96, 0x8b, 0x99, 0x96, 0x61, 0x9b, 0x99, 0x96, 0x9c, 0x52, 0x60, 0x60, 0x52, 0x8c, 0x8a, 0x20, 0x54, 0x90, 0x6f, 0x82, 0x60, 0x1c, 0x92, 0x16, 0x90, 0x61, 0x56}, 10, 8));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x89, 0x98, 0x50, 0x92, 0x82, 0x61, 0x61, 0x73, 0x96, 0x8b, 0x99, 0x96, 0x61, 0x9b, 0x99, 0x96, 0x9c, 0x52, 0x60, 0x60, 0x52, 0x8c, 0x8a, 0x20, 0x54, 0x90, 0x6f, 0x82, 0x60, 0x1c, 0x92, 0x16, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s7, s2);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const &s9 = top[-9];
            auto const h24 = aot::sha3_any<traits>(ctx, gas, s7, s9);
            gas = ctx->gas_remaining;
            uint256_t const t1 = aot::sload<traits>(ctx, gas, h24);
            uint256_t const t2 = aot::shr_c<128>(t1);
            uint256_t const t3 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const m9 = s9;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const m2 = s2;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-8] = m9;
            top[-7] = m1;
            top[-6] = uint256_t{0xac0ull};
            top[-5] = m7;
            top[-4] = m6;
            top[-3] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[-2] = m5;
            top[-1] = m4;
            top[0] = m3;
            top[1] = m2;
            top[2] = uint256_t{0x1f0eull};
            top[3] = uint256_t{0x1fa1ull};
            top[4] = t2;
            top[5] = t3;
            top[6] = m0;
            top += 6;
            MONAD_AOT_TAIL return b_3c0d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1fa1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x9a, 0x8b, 0x98, 0x61, 0x56}, 12, 2));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x9a, 0x8b, 0x98, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-11] = m0;
            top[-8] = m0;
            top[0] = m11;
            top[1] = m8;
            top += 1;
            MONAD_AOT_TAIL return b_1e39<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fb0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_1fda<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1fda(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x1fe1ull};
            top += 1;
            MONAD_AOT_TAIL return b_2c5a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2081(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j4 = aot::nonzero(t1);
            top += -1;
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_2088<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2088(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x36, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x36, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            top[1] = uint256_t{0x2090ull};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_2e98<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2090(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x92, 0x91, 0x94, 0x82, 0x94, 0x86, 0x91, 0x60, 0x82, 0x20, 0x95, 0x86, 0x82, 0x52, 0x60, 0x96, 0x60, 0x96, 0x88, 0x88, 0x52, 0x6f, 0x90, 0x61, 0x82, 0x60, 0x60, 0x88, 0x20, 0x01, 0x54, 0x16, 0x15, 0x15, 0x61, 0x61, 0x56}, 6, 11));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1013)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x92, 0x91, 0x94, 0x82, 0x94, 0x86, 0x91, 0x60, 0x82, 0x20, 0x95, 0x86, 0x82, 0x52, 0x60, 0x96, 0x60, 0x96, 0x88, 0x88, 0x52, 0x6f, 0x90, 0x61, 0x82, 0x60, 0x60, 0x88, 0x20, 0x01, 0x54, 0x16, 0x15, 0x15, 0x61, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            auto const h11 = aot::sha3_any<traits>(ctx, gas, s4, uint256_t{0xa0ull});
            gas = ctx->gas_remaining;
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, s5, h11);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s5);
            uint256_t const t2 = t1 + uint256_t{0x2ull};
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m4 = s4;
            uint256_t const m5 = s5;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-5] = m2;
            top[-4] = m3;
            top[-3] = uint256_t{0x3ull};
            top[-2] = uint256_t{0x20ull};
            top[-1] = m0;
            top[0] = m2;
            top[1] = m4;
            top[2] = m5;
            top[3] = m1;
            top[4] = h11;
            top[5] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            top[6] = m3;
            top[7] = uint256_t{0x20d2ull};
            top[8] = t6;
            top[9] = uint256_t{0x249ull};
            top += 9;
            MONAD_AOT_TAIL return b_3016<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_20d2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x93, 0x61, 0x61, 0x61, 0x56}, 5, 3));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x93, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-4] = t1;
            top[0] = m4;
            top[1] = uint256_t{0x20e8ull};
            top[2] = uint256_t{0x20dfull};
            top += 2;
            MONAD_AOT_TAIL return b_30f9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_20df(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x8d, 0x15, 0x87, 0x18, 0x61, 0x56}, 14, 2));
            if (MONAD_UNLIKELY(top - bottom < 14)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x8d, 0x15, 0x87, 0x18, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s13 = top[-13];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s13));
            uint256_t const &s6 = top[-6];
            uint256_t const t2 = s6 ^ t1;
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_20e8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x96, 0x87, 0x89, 0x16, 0x95, 0x61, 0x61, 0x61, 0x56}, 8, 5));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x96, 0x87, 0x89, 0x16, 0x95, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = s7 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-6] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[-4] = t1;
            top[1] = m6;
            top[2] = m4;
            top[3] = uint256_t{0x2115ull};
            top[4] = uint256_t{0x210dull};
            top += 4;
            MONAD_AOT_TAIL return b_3132<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_210d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x88, 0x15, 0x15, 0x61, 0x56}, 9, 2));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x88, 0x15, 0x15, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s8));
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2115(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x87, 0x61, 0x56}, 6, 4));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x87, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[1] = uint256_t{0x2121ull};
            top[2] = uint256_t{0x15ecull};
            top[3] = m5;
            top += 3;
            MONAD_AOT_TAIL return b_3328<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2121(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x85, 0x89, 0x61, 0x56}, 8, 4));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x85, 0x89, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[1] = uint256_t{0x212bull};
            top[2] = m4;
            top[3] = m7;
            top += 3;
            MONAD_AOT_TAIL return b_336e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_212b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j2 = aot::nonzero(s0);
            top += -1;
            if (j2) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x22e6); }
            MONAD_AOT_TAIL return b_2130<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2130(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x8a, 0x9b, 0x50, 0x82, 0x81, 0x9b, 0x98, 0x99, 0x9a, 0x9b, 0x52, 0x8a, 0x8a, 0x52, 0x61, 0x60, 0x60, 0x83, 0x20, 0x01, 0x54, 0x83, 0x81, 0x60, 0x1c, 0x91, 0x16, 0x8a, 0x61, 0x56}, 13, 4));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x8a, 0x9b, 0x50, 0x82, 0x81, 0x9b, 0x98, 0x99, 0x9a, 0x9b, 0x52, 0x8a, 0x8a, 0x52, 0x61, 0x60, 0x60, 0x83, 0x20, 0x01, 0x54, 0x83, 0x81, 0x60, 0x1c, 0x91, 0x16, 0x8a, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s1, s3);
            uint256_t const &s9 = top[-9];
            uint256_t const &s10 = top[-10];
            aot::mstore<traits>(ctx, gas, s9, s10);
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s1);
            uint256_t const t2 = t1 + uint256_t{0x1ull};
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const t4 = aot::shr_c<128>(t3);
            uint256_t const &s2 = top[-2];
            uint256_t const t5 = t3 & s2;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const m10 = s10;
            uint256_t const m9 = s9;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-12] = m11;
            top[-11] = m10;
            top[-10] = m9;
            top[-9] = m8;
            top[-8] = m11;
            top[0] = uint256_t{0x2156ull};
            top[1] = t4;
            top[2] = t5;
            top[3] = m11;
            top += 3;
            MONAD_AOT_TAIL return b_3c33<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2156(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x9a, 0x8b, 0x94}, 12, 1));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x9a, 0x8b, 0x94}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-11] = m0;
            top[-4] = m0;
            top[0] = m11;
            top[1] = m4;
            top += 1;
            MONAD_AOT_TAIL return b_215a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_215a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x86, 0x61, 0x56}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x86, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[1] = uint256_t{0x2163ull};
            top[2] = m5;
            top += 2;
            MONAD_AOT_TAIL return b_3c78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2163(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x85, 0x84, 0x52, 0x60, 0x8d, 0x52, 0x8c, 0x83, 0x60, 0x86, 0x20, 0x98, 0x8c, 0x85, 0x16, 0x99, 0x8a, 0x60, 0x52, 0x83, 0x52, 0x60, 0x60, 0x20, 0x60, 0x01, 0x88, 0x81, 0x54, 0x95, 0x81, 0x87, 0x16, 0x90, 0x61, 0x91, 0x61, 0x56}, 13, 9));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x85, 0x84, 0x52, 0x60, 0x8d, 0x52, 0x8c, 0x83, 0x60, 0x86, 0x20, 0x98, 0x8c, 0x85, 0x16, 0x99, 0x8a, 0x60, 0x52, 0x83, 0x52, 0x60, 0x60, 0x20, 0x60, 0x01, 0x88, 0x81, 0x54, 0x95, 0x81, 0x87, 0x16, 0x90, 0x61, 0x91, 0x61, 0x56}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, s3, s5);
            uint256_t const &s12 = top[-12];
            aot::mstore<traits>(ctx, gas, s12, uint256_t{0x2ull});
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s3);
            uint256_t const &s1 = top[-1];
            uint256_t const &s9 = top[-9];
            uint256_t const t2 = s1 & s9;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            aot::mstore<traits>(ctx, gas, s12, t1);
            uint256_t const t3 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t4 = uint256_t{0x1ull} + t3;
            uint256_t const t5 = aot::sload<traits>(ctx, gas, t4);
            uint256_t const &s4 = top[-4];
            uint256_t const t6 = t5 & s4;
            uint256_t const m12 = s12;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const m4 = s4;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-6] = t2;
            top[0] = t5;
            top[1] = m12;
            top[2] = m2;
            top[3] = m6;
            top[4] = t4;
            top[5] = m4;
            top[6] = uint256_t{0x2194ull};
            top[7] = m0;
            top[8] = t6;
            top += 8;
            MONAD_AOT_TAIL return b_3178<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2194(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x16, 0x7f, 0x80, 0x96, 0x16, 0x17, 0x90, 0x55, 0x61, 0x90, 0x61, 0x56}, 7, 1));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x16, 0x7f, 0x80, 0x96, 0x16, 0x17, 0x90, 0x55, 0x61, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 & s1;
            uint256_t const &s6 = top[-6];
            uint256_t const t2 = s6 & uint256_t{0x0ull, 0x0ull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = t2 | t1;
            uint256_t const &s2 = top[-2];
            aot::sstore<traits>(ctx, gas, s2, t3, (aot::gas_of<traits>({0x61, 0x90, 0x61, 0x56}) + 0));
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-6] = uint256_t{0x0ull, 0x0ull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            top[-3] = uint256_t{0x21c5ull};
            top[-2] = m3;
            top += -2;
            MONAD_AOT_TAIL return b_3c78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_21c5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x88, 0x87, 0x52, 0x52, 0x60, 0x85, 0x20, 0x60, 0x01, 0x90, 0x81, 0x54, 0x60, 0x1c, 0x90, 0x61, 0x91, 0x61, 0x56}, 9, 2));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x88, 0x87, 0x52, 0x52, 0x60, 0x85, 0x20, 0x60, 0x01, 0x90, 0x81, 0x54, 0x60, 0x1c, 0x90, 0x61, 0x91, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, s6, s8);
            uint256_t const &s2 = top[-2];
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s2, s1);
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s6);
            uint256_t const t2 = uint256_t{0x1ull} + t1;
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const t4 = aot::shr_c<128>(t3);
            top[-2] = t2;
            top[-1] = uint256_t{0x21e1ull};
            top[1] = t4;
            top += 1;
            MONAD_AOT_TAIL return b_3178<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_21e1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x54, 0x6f, 0x16, 0x60, 0x91, 0x90, 0x91, 0x1b, 0x7f, 0x16, 0x17, 0x90, 0x55, 0x8c, 0x83, 0x61, 0x8d, 0x61, 0x56}, 15, 3));
            if (MONAD_UNLIKELY(top - bottom < 15)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x54, 0x6f, 0x16, 0x60, 0x91, 0x90, 0x91, 0x1b, 0x7f, 0x16, 0x17, 0x90, 0x55, 0x8c, 0x83, 0x61, 0x8d, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::sload<traits>(ctx, gas, s1);
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull} & t1;
            uint256_t const &s0 = top[0];
            uint256_t const t3 = aot::shl_c<128>(s0);
            uint256_t const t4 = uint256_t{0x0ull, 0x0ull, 0xffffffffffffffffull, 0xffffffffffffffffull} & t3;
            uint256_t const t5 = t4 | t2;
            aot::sstore<traits>(ctx, gas, s1, t5, (aot::gas_of<traits>({0x8c, 0x83, 0x61, 0x8d, 0x61, 0x56}) + 0));
            uint256_t const &s14 = top[-14];
            uint256_t const m14 = s14;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            top[-1] = m14;
            top[0] = m4;
            top[1] = uint256_t{0x222bull};
            top[2] = m12;
            top += 2;
            MONAD_AOT_TAIL return b_3c78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_222b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x88, 0x87, 0x52, 0x52, 0x60, 0x85, 0x20, 0x60, 0x01, 0x91, 0x86, 0x83, 0x54, 0x92, 0x81, 0x84, 0x16, 0x90, 0x61, 0x91, 0x61, 0x56}, 9, 4));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x88, 0x87, 0x52, 0x52, 0x60, 0x85, 0x20, 0x60, 0x01, 0x91, 0x86, 0x83, 0x54, 0x92, 0x81, 0x84, 0x16, 0x90, 0x61, 0x91, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, s6, s8);
            uint256_t const &s2 = top[-2];
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s2, s1);
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s6);
            uint256_t const t2 = uint256_t{0x1ull} + t1;
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const &s7 = top[-7];
            uint256_t const t4 = t3 & s7;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const m7 = s7;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-3] = t2;
            top[-2] = t3;
            top[-1] = m3;
            top[0] = m7;
            top[1] = uint256_t{0x2249ull};
            top[2] = m0;
            top[3] = t4;
            top += 3;
            MONAD_AOT_TAIL return b_3178<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2249(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x61, 0x90, 0x85, 0x89, 0x61, 0x56}, 13, 0));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x61, 0x90, 0x85, 0x89, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 & s1;
            uint256_t const &s3 = top[-3];
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s3 & s2;
            uint256_t const t3 = t2 | t1;
            uint256_t const &s4 = top[-4];
            aot::sstore<traits>(ctx, gas, s4, t3, (aot::gas_of<traits>({0x61, 0x90, 0x85, 0x89, 0x61, 0x56}) + 0));
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            top[-5] = uint256_t{0x225aull};
            top[-4] = m5;
            top[-3] = m9;
            top[-2] = m12;
            top += -2;
            MONAD_AOT_TAIL return b_367c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_225a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x2262ull};
            top += 1;
            MONAD_AOT_TAIL return b_3289<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2262(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = uint256_t{0x226bull};
            top[1] = m1;
            top += 1;
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_226b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x82, 0x52, 0x8a, 0x52, 0x60, 0x90, 0x20, 0x90, 0x80, 0x60, 0x83, 0x01, 0x54, 0x16, 0x91, 0x54, 0x16, 0x10, 0x15, 0x61, 0x61, 0x56}, 11, 2));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x82, 0x52, 0x8a, 0x52, 0x60, 0x90, 0x20, 0x90, 0x80, 0x60, 0x83, 0x01, 0x54, 0x16, 0x91, 0x54, 0x16, 0x10, 0x15, 0x61, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s1, s3);
            uint256_t const &s10 = top[-10];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s10, s0);
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s1);
            uint256_t const t2 = t1 + uint256_t{0x1ull};
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = t3 & s2;
            uint256_t const t5 = aot::sload<traits>(ctx, gas, t1);
            uint256_t const t6 = t5 & s2;
            uint256_t const t7 = aot::from_bool(t6 < t4);
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            top[-2] = t8;
            top[-1] = uint256_t{0x2289ull};
            top += -1;
            MONAD_AOT_TAIL return b_3250<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2289(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x91, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = uint256_t{0x2292ull};
            top[1] = m1;
            top += 1;
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2292(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x80, 0x51, 0x33, 0x81, 0x52, 0x60, 0x81, 0x01, 0x88, 0x90, 0x52, 0x90, 0x81, 0x01, 0x8a, 0x90, 0x52, 0x7f, 0x90, 0x60, 0x90, 0xa4, 0x51, 0x16, 0x91, 0x61, 0x92, 0x61, 0x56}, 9, 4));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x80, 0x51, 0x33, 0x81, 0x52, 0x60, 0x81, 0x01, 0x88, 0x90, 0x52, 0x90, 0x81, 0x01, 0x8a, 0x90, 0x52, 0x7f, 0x90, 0x60, 0x90, 0xa4, 0x51, 0x16, 0x91, 0x61, 0x92, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.sender);
            aot::mstore<traits>(ctx, gas, t1, t2);
            uint256_t const t3 = t1 + uint256_t{0x20ull};
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, t3, s5);
            uint256_t const t4 = t1 + uint256_t{0x40ull};
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, t4, s8);
            uint256_t const k23_1 = uint256_t{0x60ull};
            uint256_t const k23_2 = uint256_t{0xdcd85c9b5fd42a43ull, 0x4a648f7097a16240ull, 0x4a87dfe815a5edaull, 0x570954540bed6b13ull};
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            ctx->gas_remaining = gas;
            runtime::log4<traits>(ctx, &t1, &k23_1, &k23_2, &s0, &s1, &s2);
            gas = ctx->gas_remaining;
            uint256_t const &s3 = top[-3];
            uint256_t const t5 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const t6 = t5 & s4;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-6] = uint256_t{0x22d8ull};
            top[-4] = m6;
            top[-3] = t6;
            top += -3;
            MONAD_AOT_TAIL return b_394a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_22d8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x92, 0x83, 0x52, 0x82, 0x01, 0x52, 0x60, 0x90, 0xf3}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x92, 0x83, 0x52, 0x82, 0x01, 0x52, 0x60, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t1, s2);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = t1 + s0;
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t2, s1);
            aot::finish(ctx, gas, StatusCode::Success, t1, uint256_t{0x40ull});
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_231c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_2346<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2346(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x7f, 0x60, 0x60, 0x35, 0x61, 0x73, 0x85, 0x54, 0x16, 0x33, 0x14, 0x61, 0x61, 0x56}, 1, 7));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x7f, 0x60, 0x60, 0x35, 0x61, 0x73, 0x85, 0x54, 0x16, 0x33, 0x14, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::sload<traits>(ctx, gas, s0);
            uint256_t const t3 = t2 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t4 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t5 = aot::from_bool(t4 == t3);
            top[1] = uint256_t{0x851939405ec29139ull, 0x9bde997260ff3dbull, 0x70c630f6575072d6ull, 0x297b80e7a896fad4ull};
            top[2] = uint256_t{0x20ull};
            top[3] = t1;
            top[4] = uint256_t{0x2390ull};
            top[5] = t5;
            top[6] = uint256_t{0x249ull};
            top += 6;
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2f08);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2438(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_2461<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2461(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x73, 0x60, 0x54, 0x16, 0x60, 0x51, 0x90, 0x81, 0x52, 0xf3}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x73, 0x60, 0x54, 0x16, 0x60, 0x51, 0x90, 0x81, 0x52, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::sload<traits>(ctx, gas, uint256_t{0x1ull});
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t3, t2);
            aot::finish(ctx, gas, StatusCode::Success, t3, uint256_t{0x20ull});
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_248a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_24b3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_24b3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x51, 0x7f, 0x81, 0x52, 0xf3}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x51, 0x7f, 0x81, 0x52, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x1e0eb9f28cafdd2dull, 0xc7a4a17b4db99be4ull, 0x12b671d38548b711ull, 0xec6ac4ec64693757ull});
            aot::finish(ctx, gas, StatusCode::Success, t1, uint256_t{0x20ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_24dc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j4 = aot::nonzero(t1);
            top += -1;
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_24e3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_24e3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_250d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_250d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x91, 0x60, 0x35, 0x81, 0x52, 0x60, 0x60, 0x52, 0x20, 0x73, 0x80, 0x82, 0x54, 0x16, 0x91, 0x81, 0x60, 0x82, 0x01, 0x54, 0x16, 0x91, 0x60, 0x81, 0x60, 0x84, 0x01, 0x54, 0x16, 0x91, 0x60, 0x84, 0x01, 0x54, 0x16, 0x92, 0x01, 0x54, 0x92, 0x60, 0x51, 0x94, 0x85, 0x52, 0x60, 0x85, 0x01, 0x52, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0xf3}, 1, 8));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x91, 0x60, 0x35, 0x81, 0x52, 0x60, 0x60, 0x52, 0x20, 0x73, 0x80, 0x82, 0x54, 0x16, 0x91, 0x81, 0x60, 0x82, 0x01, 0x54, 0x16, 0x91, 0x60, 0x81, 0x60, 0x84, 0x01, 0x54, 0x16, 0x91, 0x60, 0x84, 0x01, 0x54, 0x16, 0x92, 0x01, 0x54, 0x92, 0x60, 0x51, 0x94, 0x85, 0x52, 0x60, 0x85, 0x01, 0x52, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0xf3}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, t1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x8ull});
            uint256_t const t2 = aot::sha3_n<traits, 64>(ctx, gas, s0);
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t5 = t2 + uint256_t{0x1ull};
            uint256_t const t6 = aot::sload<traits>(ctx, gas, t5);
            uint256_t const t7 = t6 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t8 = t2 + uint256_t{0x2ull};
            uint256_t const t9 = aot::sload<traits>(ctx, gas, t8);
            uint256_t const t10 = t9 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t11 = t2 + uint256_t{0x3ull};
            uint256_t const t12 = aot::sload<traits>(ctx, gas, t11);
            uint256_t const t13 = t12 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t14 = t2 + uint256_t{0x4ull};
            uint256_t const t15 = aot::sload<traits>(ctx, gas, t14);
            uint256_t const t16 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t16, t4);
            uint256_t const t17 = t16 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t17, t7);
            uint256_t const t18 = t16 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t18, t10);
            uint256_t const t19 = t16 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t19, t13);
            uint256_t const t20 = t16 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t20, t15);
            aot::finish(ctx, gas, StatusCode::Success, t16, uint256_t{0xa0ull});
            return;
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2575(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0xc0ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_259f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_259f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x36, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x36, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            top[1] = uint256_t{0x25a7ull};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_2d50<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2697(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_336e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_26fe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x100ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_2729<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2729(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x36, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x36, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            top[1] = uint256_t{0x2731ull};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_2d50<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2750(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0x275dull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_2de8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_284b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x91, 0x85, 0x91, 0x60, 0x51, 0x93, 0x84, 0x92, 0x83, 0x92, 0x7f, 0x84, 0x52, 0x88, 0x60, 0x85, 0x01, 0x61, 0x56}, 5, 8));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x91, 0x85, 0x91, 0x60, 0x51, 0x93, 0x84, 0x92, 0x83, 0x92, 0x7f, 0x84, 0x52, 0x88, 0x60, 0x85, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xb1022fdf00000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-1] = t1;
            top[0] = m4;
            top[1] = t1;
            top[2] = t1;
            top[3] = uint256_t{0x2885ull};
            top[4] = m1;
            top[5] = m0;
            top[6] = m3;
            top[7] = t2;
            top += 7;
            MONAD_AOT_TAIL return b_319c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2892(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            bool const j1 = aot::nonzero(s0);
            top += -1;
            if (j1) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x289c); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2896);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_28c8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x36, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x36, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            top[1] = uint256_t{0x28d0ull};
            top[2] = t1;
            top += 2;
            MONAD_AOT_TAIL return b_2e16<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2950(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x81, 0x86, 0x52, 0x80, 0x88, 0x52, 0x61, 0x60, 0x60, 0x88, 0x20, 0x01, 0x54, 0x8a, 0x81, 0x60, 0x1c, 0x91, 0x16, 0x8c, 0x61, 0x56}, 12, 3));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x81, 0x86, 0x52, 0x80, 0x88, 0x52, 0x61, 0x60, 0x60, 0x88, 0x20, 0x01, 0x54, 0x8a, 0x81, 0x60, 0x1c, 0x91, 0x16, 0x8c, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s7, s3);
            uint256_t const &s9 = top[-9];
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s9, s2);
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s7);
            uint256_t const t2 = t1 + uint256_t{0x1ull};
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const t4 = aot::shr_c<128>(t3);
            uint256_t const &s10 = top[-10];
            uint256_t const t5 = t3 & s10;
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            top[-1] = uint256_t{0x296full};
            top[0] = t4;
            top[1] = t5;
            top[2] = m11;
            top += 2;
            MONAD_AOT_TAIL return b_3be8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2a5d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x83, 0x60, 0x95, 0x61, 0x92, 0x51, 0x16, 0x30, 0x90, 0x33, 0x90, 0x61, 0x56}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x83, 0x60, 0x95, 0x61, 0x92, 0x51, 0x16, 0x30, 0x90, 0x33, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const &s7 = top[-7];
            uint256_t const t2 = t1 & s7;
            uint256_t const t3 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t4 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-7] = uint256_t{0x40ull};
            top[-3] = uint256_t{0x1070ull};
            top[-2] = m6;
            top[-1] = t3;
            top[0] = t4;
            top[1] = t2;
            top += 1;
            MONAD_AOT_TAIL return b_3ab9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2a7a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x91, 0x80, 0x91, 0x61, 0x93, 0x60, 0x51, 0x94, 0x85, 0x92, 0x83, 0x92, 0x7f, 0x84, 0x52, 0x8b, 0x60, 0x85, 0x01, 0x61, 0x56}, 7, 8));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x91, 0x80, 0x91, 0x61, 0x93, 0x60, 0x51, 0x94, 0x85, 0x92, 0x83, 0x92, 0x7f, 0x84, 0x52, 0x8b, 0x60, 0x85, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x5b4591c00000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-2] = t1;
            top[-1] = m2;
            top[0] = m2;
            top[1] = t1;
            top[2] = t1;
            top[3] = uint256_t{0x2ab5ull};
            top[4] = m1;
            top[5] = m0;
            top[6] = m6;
            top[7] = t2;
            top += 7;
            MONAD_AOT_TAIL return b_319c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ac3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x95, 0x61, 0x92, 0x86, 0x92, 0x60, 0x98, 0x61, 0x57}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x95, 0x61, 0x92, 0x86, 0x92, 0x60, 0x98, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            bool const j9 = aot::nonzero(s1);
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-7] = uint256_t{0x40ull};
            top[-3] = uint256_t{0x1070ull};
            top[-2] = m6;
            top[-1] = m7;
            top[0] = m3;
            top[1] = m2;
            top += 1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2adc); }
            MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2ad2);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2b20(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j4 = aot::nonzero(t1);
            top += -1;
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_2b27<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b27(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0xa0ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_2b51<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b51(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x36, 0x61, 0x56}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x36, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            top[1] = uint256_t{0x4bbull};
            top[2] = uint256_t{0x2b5cull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2d50<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2b5c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x20, 0x90, 0x81, 0x84, 0x52, 0x60, 0x60, 0x52, 0x61, 0x6f, 0x60, 0x60, 0x87, 0x20, 0x01, 0x54, 0x16, 0x15, 0x15, 0x61, 0x61, 0x56}, 3, 6));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x20, 0x90, 0x81, 0x84, 0x52, 0x60, 0x60, 0x52, 0x61, 0x6f, 0x60, 0x60, 0x87, 0x20, 0x01, 0x54, 0x16, 0x15, 0x15, 0x61, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            auto const h3 = aot::sha3_any<traits>(ctx, gas, s0, uint256_t{0xa0ull});
            gas = ctx->gas_remaining;
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, h3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, s2);
            uint256_t const t2 = t1 + uint256_t{0x2ull};
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const m0 = s0;
            top[0] = h3;
            top[1] = m0;
            top[2] = uint256_t{0x2697ull};
            top[3] = t6;
            top[4] = uint256_t{0x249ull};
            top += 4;
            MONAD_AOT_TAIL return b_3016<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b97(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x7f, 0x36, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j6 = aot::nonzero(t3);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1b8); }
            MONAD_AOT_TAIL return b_2bc1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2bc1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x2c2full};
            top[2] = uint256_t{0x2bcbull};
            top += 2;
            MONAD_AOT_TAIL return b_2c5a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2c5a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2c7c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2c7c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2c9f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2cc2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2cc3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x81, 0x11, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xffffffffffffffffull} < s0);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a35); }
            MONAD_AOT_TAIL return b_2cd3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2cd3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2cd7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a35); }
            MONAD_AOT_TAIL return b_2cef<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2cef(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2cf3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x01, 0x90, 0x81, 0x10, 0x67, 0x82, 0x11, 0x17, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x40ull};
            uint256_t const t2 = aot::from_bool(t1 < s0);
            uint256_t const t3 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            uint256_t const t4 = t3 | t2;
            bool const j12 = aot::nonzero(t4);
            top[0] = t1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a35); }
            MONAD_AOT_TAIL return b_2d0b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d0b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2d0f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j17) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a35); }
            MONAD_AOT_TAIL return b_2d4c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d4c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2d50(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x60, 0x91, 0x01, 0x12, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x60, 0x91, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0xa0ull}));
            bool const j7 = aot::nonzero(t2);
            top += -1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2d7b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d7b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            top[2] = uint256_t{0x2d87ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2cd7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2d87(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x73, 0x60, 0x35, 0x81, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x73, 0x60, 0x35, 0x81, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t3 = t1 - t2;
            bool const j11 = aot::nonzero(t3);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[1] = m1;
            top[2] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[3] = t1;
            top += 3;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2daa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2daa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x52, 0x60, 0x35, 0x81, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x52, 0x60, 0x35, 0x81, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s2, s0);
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 & s1;
            uint256_t const t3 = t1 - t2;
            bool const j10 = aot::nonzero(t3);
            top[0] = t1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2db8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2db8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x83, 0x01, 0x52, 0x60, 0x35, 0x81, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x83, 0x01, 0x52, 0x60, 0x35, 0x81, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = t2 & s1;
            uint256_t const t4 = t2 - t3;
            bool const j12 = aot::nonzero(t4);
            top[0] = t2;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2dc9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2dc9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x83, 0x01, 0x52, 0x60, 0x35, 0x90, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x83, 0x01, 0x52, 0x60, 0x35, 0x90, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0x40ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x64ull});
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = t2 & s1;
            uint256_t const t4 = t2 - t3;
            bool const j12 = aot::nonzero(t4);
            top[-1] = t2;
            top += -1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2dda<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2dda(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x82, 0x01, 0x52, 0x60, 0x60, 0x35, 0x91, 0x01, 0x52, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x82, 0x01, 0x52, 0x60, 0x60, 0x35, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x60ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0x84ull});
            uint256_t const t3 = s1 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top += -3;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2de8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2df5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2df5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2e07<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e07(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2e15<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e15(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2e16(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x7f, 0x82, 0x01, 0x12, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x7f, 0x82, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x120ull}));
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2e42<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e42(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x81, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x2e4aull};
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_2d50<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2e4a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x60, 0x35, 0x91, 0x60, 0x35, 0x91, 0x60, 0x35, 0x73, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x60, 0x35, 0x91, 0x60, 0x35, 0x91, 0x60, 0x35, 0x73, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0xc4ull});
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0xe4ull});
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t5 = t3 - t4;
            bool const j16 = aot::nonzero(t5);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = t2;
            top[1] = m1;
            top[2] = m2;
            top[3] = t3;
            top += 3;
            if (j16) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2e74<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e74(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x91, 0x61, 0x35, 0x90, 0x67, 0x82, 0x11, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x91, 0x61, 0x35, 0x90, 0x67, 0x82, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x104ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j8 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[0] = t1;
            top[1] = m2;
            top += 1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2e89<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2e89(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x91, 0x60, 0x01, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x91, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = uint256_t{0x4ull} + s1;
            top[-1] = uint256_t{0x2e94ull};
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_2de8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2e94(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x91, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x91, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m1;
            top[-1] = m0;
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2e98(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x7f, 0x82, 0x01, 0x12, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x7f, 0x82, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x120ull}));
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2ec4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ec4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x61, 0x56}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x2eccull};
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_2d50<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2ecc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x60, 0x35, 0x90, 0x60, 0x35, 0x90, 0x73, 0x90, 0x60, 0x35, 0x82, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x60, 0x35, 0x90, 0x60, 0x35, 0x90, 0x73, 0x90, 0x60, 0x35, 0x82, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0xa4ull});
            uint256_t const t2 = aot::calldataload(ctx, uint256_t{0xc4ull});
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0xe4ull});
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t5 = t3 - t4;
            bool const j18 = aot::nonzero(t5);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = m0;
            top[0] = t1;
            top[1] = t2;
            top[2] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[3] = m1;
            top[4] = t3;
            top += 4;
            if (j18) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2ef8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2ef8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x91, 0x61, 0x35, 0x90, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x91, 0x61, 0x35, 0x90, 0x81, 0x16, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x104ull});
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = t1 & s2;
            uint256_t const t3 = t1 - t2;
            bool const j9 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[0] = t1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_2f06<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2f06(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2f41(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2f49); }
            MONAD_AOT_TAIL return b_2f47<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2f47(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x56}, 2, 0));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2f8d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x7f, 0x60, 0x83, 0x60, 0x60, 0x80, 0x96, 0x86, 0x01, 0x01, 0x52, 0x01, 0x16, 0x81, 0x01, 0x03, 0x01, 0x90, 0xfd}, 6, 4));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x7f, 0x60, 0x83, 0x60, 0x60, 0x80, 0x96, 0x86, 0x01, 0x01, 0x52, 0x01, 0x16, 0x81, 0x01, 0x03, 0x01, 0x90, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s3 + s4;
            uint256_t const t2 = t1 + uint256_t{0x44ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x0ull});
            uint256_t const t3 = s4 + uint256_t{0x1full};
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t5 = s3 + t4;
            uint256_t const t6 = t5 - s3;
            uint256_t const t7 = t6 + uint256_t{0x44ull};
            uint256_t const &s5 = top[-5];
            aot::finish(ctx, gas, StatusCode::Revert, s5, t7);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3016(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x3023ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3023(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x12ull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x6564000000000000ull, 0x6f74206372656174ull, 0x6d61726b6574206eull});
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_304f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x92, 0x91, 0x61, 0x90, 0x61, 0x83, 0x61, 0x81, 0x01, 0x96, 0x60, 0x80, 0x91, 0x73, 0x80, 0x82, 0x51, 0x16, 0x85, 0x52, 0x80, 0x60, 0x83, 0x01, 0x51, 0x16, 0x60, 0x86, 0x01, 0x52, 0x80, 0x60, 0x83, 0x01, 0x51, 0x16, 0x60, 0x86, 0x01, 0x52, 0x60, 0x82, 0x01, 0x51, 0x16, 0x60, 0x85, 0x01, 0x52, 0x01, 0x51, 0x91, 0x01, 0x52, 0x56}, 4, 10));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x92, 0x91, 0x61, 0x90, 0x61, 0x83, 0x61, 0x81, 0x01, 0x96, 0x60, 0x80, 0x91, 0x73, 0x80, 0x82, 0x51, 0x16, 0x85, 0x52, 0x80, 0x60, 0x83, 0x01, 0x51, 0x16, 0x60, 0x86, 0x01, 0x52, 0x80, 0x60, 0x83, 0x01, 0x51, 0x16, 0x60, 0x86, 0x01, 0x52, 0x60, 0x82, 0x01, 0x51, 0x16, 0x60, 0x85, 0x01, 0x52, 0x01, 0x51, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x160ull};
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const t3 = t2 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore<traits>(ctx, gas, s0, t3);
            uint256_t const t4 = s1 + uint256_t{0x20ull};
            uint256_t const t5 = aot::mload<traits>(ctx, gas, t4);
            uint256_t const t6 = t5 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t7 = s0 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t7, t6);
            uint256_t const t8 = s1 + uint256_t{0x40ull};
            uint256_t const t9 = aot::mload<traits>(ctx, gas, t8);
            uint256_t const t10 = t9 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t11 = s0 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t11, t10);
            uint256_t const t12 = s1 + uint256_t{0x60ull};
            uint256_t const t13 = aot::mload<traits>(ctx, gas, t12);
            uint256_t const t14 = t13 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            uint256_t const t15 = s0 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t15, t14);
            uint256_t const t16 = s1 + uint256_t{0x80ull};
            uint256_t const t17 = aot::mload<traits>(ctx, gas, t16);
            uint256_t const t18 = s0 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t18, t17);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-3] = t1;
            top[-2] = m3;
            top[-1] = m0;
            top[0] = uint256_t{0x140ull};
            top[1] = m2;
            top += 1;
            MONAD_AOT_TAIL return b_30a9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_30a9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x54, 0x91, 0x6f, 0x92, 0x83, 0x81, 0x16, 0x60, 0x87, 0x01, 0x52, 0x60, 0x1c, 0x60, 0x86, 0x01, 0x52, 0x60, 0x81, 0x01, 0x54, 0x83, 0x81, 0x16, 0x60, 0x87, 0x01, 0x52, 0x60, 0x1c, 0x61, 0x86, 0x01, 0x52, 0x01, 0x54, 0x90, 0x81, 0x16, 0x61, 0x84, 0x01, 0x52, 0x60, 0x1c, 0x91, 0x01, 0x52, 0x56}, 4, 6));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x54, 0x91, 0x6f, 0x92, 0x83, 0x81, 0x16, 0x60, 0x87, 0x01, 0x52, 0x60, 0x1c, 0x60, 0x86, 0x01, 0x52, 0x60, 0x81, 0x01, 0x54, 0x83, 0x81, 0x16, 0x60, 0x87, 0x01, 0x52, 0x60, 0x1c, 0x61, 0x86, 0x01, 0x52, 0x01, 0x54, 0x90, 0x81, 0x16, 0x61, 0x84, 0x01, 0x52, 0x60, 0x1c, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::sload<traits>(ctx, gas, s0);
            uint256_t const t2 = t1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = s2 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = aot::shr_c<128>(t1);
            uint256_t const t5 = s2 + uint256_t{0xc0ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const t6 = s0 + uint256_t{0x1ull};
            uint256_t const t7 = aot::sload<traits>(ctx, gas, t6);
            uint256_t const t8 = t7 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t9 = s2 + uint256_t{0xe0ull};
            aot::mstore<traits>(ctx, gas, t9, t8);
            uint256_t const t10 = aot::shr_c<128>(t7);
            uint256_t const t11 = s2 + uint256_t{0x100ull};
            aot::mstore<traits>(ctx, gas, t11, t10);
            uint256_t const t12 = s0 + uint256_t{0x2ull};
            uint256_t const t13 = aot::sload<traits>(ctx, gas, t12);
            uint256_t const t14 = t13 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t15 = s2 + uint256_t{0x120ull};
            aot::mstore<traits>(ctx, gas, t15, t14);
            uint256_t const t16 = aot::shr_c<128>(t13);
            uint256_t const &s1 = top[-1];
            uint256_t const t17 = s2 + s1;
            aot::mstore<traits>(ctx, gas, t17, t16);
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top += -4;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_30f9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x3106ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3106(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x12ull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x7574000000000000ull, 0x74656e7420696e70ull, 0x696e636f6e736973ull});
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3132(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x313full};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_313f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0xcull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x7265737300000000ull, 0x7a65726f20616464ull});
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_316b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x90, 0x82, 0x01, 0x80, 0x92, 0x11, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x90, 0x82, 0x01, 0x80, 0x92, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            uint256_t const t2 = aot::from_bool(t1 < s0);
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[-1] = m2;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_3177<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3177(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3178(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x90, 0x91, 0x6f, 0x80, 0x80, 0x94, 0x16, 0x91, 0x16, 0x01, 0x91, 0x82, 0x11, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x90, 0x91, 0x6f, 0x80, 0x80, 0x94, 0x16, 0x91, 0x16, 0x01, 0x91, 0x82, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t3 = t2 + t1;
            uint256_t const t4 = aot::from_bool(uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull} < t3);
            bool const j16 = aot::nonzero(t4);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t3;
            top[-1] = m2;
            top += -1;
            if (j16) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_319b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_319b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_319c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x83, 0x60, 0x94, 0x60, 0x92, 0x7f, 0x94, 0x86, 0x52, 0x60, 0x60, 0x87, 0x01, 0x52, 0x81, 0x60, 0x87, 0x01, 0x52, 0x86, 0x86, 0x01, 0x37, 0x60, 0x85, 0x82, 0x86, 0x01, 0x01, 0x52, 0x01, 0x16, 0x01, 0x01, 0x90, 0x56}, 5, 6));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x83, 0x60, 0x94, 0x60, 0x92, 0x7f, 0x94, 0x86, 0x52, 0x60, 0x60, 0x87, 0x01, 0x52, 0x81, 0x60, 0x87, 0x01, 0x52, 0x86, 0x86, 0x01, 0x37, 0x60, 0x85, 0x82, 0x86, 0x01, 0x01, 0x52, 0x01, 0x16, 0x01, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s0, s1);
            uint256_t const t1 = s0 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x40ull});
            uint256_t const t2 = s0 + uint256_t{0x40ull};
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, t2, s3);
            uint256_t const t3 = s0 + uint256_t{0x60ull};
            uint256_t const &s2 = top[-2];
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t3, &s2, &s3);
            gas = ctx->gas_remaining;
            uint256_t const t4 = s0 + s3;
            uint256_t const t5 = t4 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t5, uint256_t{0x0ull});
            uint256_t const t6 = s3 + uint256_t{0x1full};
            uint256_t const t7 = t6 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t8 = t7 + s0;
            uint256_t const t9 = t8 + uint256_t{0x60ull};
            uint256_t const &s4 = top[-4];
            uint64_t const jt = aot::jump_offset(s4);
            top[-4] = t9;
            top += -4;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_31e8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x31f5ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_31f5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0xcull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x697a656400000000ull, 0x756e617574686f72ull});
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3221(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x90, 0x82, 0x03, 0x91, 0x82, 0x11, 0x61, 0x57}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x90, 0x82, 0x03, 0x91, 0x82, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const t2 = aot::from_bool(s0 < t1);
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[-1] = m2;
            top += -1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_322d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_322d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_322e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x6f, 0x91, 0x82, 0x16, 0x90, 0x82, 0x16, 0x03, 0x91, 0x90, 0x82, 0x11, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x6f, 0x91, 0x82, 0x16, 0x90, 0x82, 0x16, 0x03, 0x91, 0x90, 0x82, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull} & s1;
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull} & s0;
            uint256_t const t3 = t2 - t1;
            uint256_t const t4 = aot::from_bool(uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull} < t3);
            bool const j14 = aot::nonzero(t4);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t3;
            top[-1] = m2;
            top += -1;
            if (j14) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_324f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_324f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3250(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x325dull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_325d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x16ull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x7569646974790000ull, 0x69656e74206c6971ull, 0x696e737566666963ull});
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3289(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x3296ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3296(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x17ull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x6c61746572616c00ull, 0x69656e7420636f6cull, 0x696e737566666963ull});
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_32c2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x32cfull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_32cf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0xbull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x6574730000000000ull, 0x7a65726f20617373ull});
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_32fb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x81, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x81, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(s0 == uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_3323<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3323(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3328(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x73, 0x16, 0x80, 0x33, 0x14, 0x90, 0x81, 0x15, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x73, 0x16, 0x80, 0x33, 0x14, 0x90, 0x81, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s0;
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t3 = aot::from_bool(t2 == t1);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j10 = aot::nonzero(t4);
            top[0] = t3;
            top[1] = t1;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return b_334c<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3349<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3349(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_334c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x60, 0x52, 0x60, 0x60, 0x52, 0x60, 0x60, 0x20, 0x33, 0x60, 0x52, 0x60, 0x52, 0x60, 0x60, 0x60, 0x20, 0x54, 0x16, 0x90, 0x56}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x60, 0x52, 0x60, 0x60, 0x52, 0x60, 0x60, 0x20, 0x33, 0x60, 0x52, 0x60, 0x52, 0x60, 0x60, 0x60, 0x20, 0x54, 0x16, 0x90, 0x56}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, s0);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x6ull});
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.sender);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t1);
            uint256_t const t3 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t4 = aot::sload<traits>(ctx, gas, t3);
            uint256_t const t5 = t4 & uint256_t{0xffull};
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t5;
            top += -2;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_336e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x90, 0x60, 0x90, 0x80, 0x82, 0x52, 0x60, 0x91, 0x60, 0x92, 0x80, 0x84, 0x52, 0x6f, 0x93, 0x60, 0x93, 0x61, 0x86, 0x60, 0x87, 0x87, 0x20, 0x01, 0x54, 0x16, 0x42, 0x61, 0x56}, 3, 10));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x90, 0x60, 0x90, 0x80, 0x82, 0x52, 0x60, 0x91, 0x60, 0x92, 0x80, 0x84, 0x52, 0x6f, 0x93, 0x60, 0x93, 0x61, 0x86, 0x60, 0x87, 0x87, 0x20, 0x01, 0x54, 0x16, 0x42, 0x61, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, s1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t2 = t1 + uint256_t{0x2ull};
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const t4 = t3 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const m1 = s1;
            top[-2] = m0;
            top[-1] = m2;
            top[0] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            top[1] = uint256_t{0x40ull};
            top[2] = uint256_t{0x0ull};
            top[3] = uint256_t{0x3ull};
            top[4] = uint256_t{0x20ull};
            top[5] = m1;
            top[6] = uint256_t{0x33a6ull};
            top[7] = t4;
            top[8] = t5;
            top += 8;
            MONAD_AOT_TAIL return b_3221<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_33a6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_3671<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_33ad<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_33ad(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x73, 0x90, 0x81, 0x60, 0x8b, 0x01, 0x51, 0x16, 0x80, 0x61, 0x57}, 9, 4));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x73, 0x90, 0x81, 0x60, 0x8b, 0x01, 0x51, 0x16, 0x80, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const t1 = s8 + uint256_t{0x60ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = t2 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            bool const j10 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[1] = m0;
            top[2] = t3;
            top += 2;
            if (j10) { MONAD_AOT_TAIL return b_3409<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_33cf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_33cf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x60, 0x95, 0x96, 0x97, 0x50, 0x83, 0x52, 0x52, 0x20, 0x01, 0x90, 0x42, 0x16, 0x7f, 0x82, 0x54, 0x16, 0x17, 0x90, 0x55, 0x56}, 11, 0));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x60, 0x95, 0x96, 0x97, 0x50, 0x83, 0x52, 0x52, 0x20, 0x01, 0x90, 0x42, 0x16, 0x7f, 0x82, 0x54, 0x16, 0x17, 0x90, 0x55, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s6, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, s4, s5);
            uint256_t const &s7 = top[-7];
            auto const h12 = aot::sha3_any<traits>(ctx, gas, s6, s7);
            gas = ctx->gas_remaining;
            uint256_t const t1 = h12 + uint256_t{0x2ull};
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.tx_context->block_timestamp)};
            uint256_t const &s8 = top[-8];
            uint256_t const t3 = t2 & s8;
            uint256_t const t4 = aot::sload<traits>(ctx, gas, t1);
            uint256_t const t5 = t4 & uint256_t{0x0ull, 0x0ull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t6 = t5 | t3;
            aot::sstore<traits>(ctx, gas, t1, t6, (aot::gas_of<traits>({0x56}) + 0));
            uint256_t const &s9 = top[-9];
            uint64_t const jt = aot::jump_offset(s9);
            top += -11;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3409(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x85, 0x91, 0x85, 0x89, 0x52, 0x87, 0x83, 0x52, 0x89, 0x89, 0x20, 0x89, 0x8b, 0x51, 0x9e, 0x8f, 0x94, 0x85, 0x93, 0x84, 0x92, 0x7f, 0x84, 0x52, 0x60, 0x84, 0x01, 0x61, 0x56}, 11, 10));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x85, 0x91, 0x85, 0x89, 0x52, 0x87, 0x83, 0x52, 0x89, 0x89, 0x20, 0x89, 0x8b, 0x51, 0x9e, 0x8f, 0x94, 0x85, 0x93, 0x84, 0x92, 0x7f, 0x84, 0x52, 0x60, 0x84, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s6, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, s4, s5);
            uint256_t const &s7 = top[-7];
            auto const h12 = aot::sha3_any<traits>(ctx, gas, s6, s7);
            gas = ctx->gas_remaining;
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s7);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x9451fed400000000ull});
            uint256_t const t2 = t1 + uint256_t{0x4ull};
            uint256_t const m4 = s4;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m6 = s6;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[-10] = t1;
            top[0] = m4;
            top[1] = t1;
            top[2] = m0;
            top[3] = t1;
            top[4] = m6;
            top[5] = t1;
            top[6] = uint256_t{0x344dull};
            top[7] = h12;
            top[8] = m10;
            top[9] = t2;
            top += 9;
            MONAD_AOT_TAIL return b_304f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_344d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x03, 0x92, 0x5a, 0xf1, 0x99, 0x8a, 0x15, 0x61, 0x57}, 17, 0));
            if (MONAD_UNLIKELY(top - bottom < 17)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x03, 0x92, 0x5a, 0xf1, 0x99, 0x8a, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xf1, 0x99, 0x8a, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const &s4 = top[-4];
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            uint256_t const &s5 = top[-5];
            uint256_t const &s6 = top[-6];
            auto const c4 = aot::call<traits>(ctx, gas, t2, s4, s2, s3, t1, s5, s6, (aot::gas_of<traits>({0x99, 0x8a, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t3 = aot::from_bool(!aot::nonzero(c4));
            bool const j9 = aot::nonzero(t3);
            uint256_t const &s16 = top[-16];
            uint256_t const m16 = s16;
            top[-16] = c4;
            top[-6] = m16;
            top += -6;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3667); }
            MONAD_AOT_TAIL return b_3459<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3459(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x86, 0x9a, 0x61, 0x57}, 11, 2));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x86, 0x9a, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s10 = top[-10];
            bool const j3 = aot::nonzero(s10);
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-10] = m6;
            if (j3) { MONAD_AOT_TAIL return b_3637<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_345f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_345f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x60, 0x88, 0x99, 0x9a, 0x61, 0x87, 0x89, 0x87, 0x96, 0x89, 0x88, 0x60, 0x9f, 0x8f, 0x7f, 0x9a, 0x83, 0x87, 0x52, 0x87, 0x85, 0x52, 0x61, 0x61, 0x84, 0x60, 0x85, 0x8b, 0x20, 0x01, 0x54, 0x16, 0x92, 0x8c, 0x61, 0x56}, 11, 16));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1008)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x60, 0x88, 0x99, 0x9a, 0x61, 0x87, 0x89, 0x87, 0x96, 0x89, 0x88, 0x60, 0x9f, 0x8f, 0x7f, 0x9a, 0x83, 0x87, 0x52, 0x87, 0x85, 0x52, 0x61, 0x61, 0x84, 0x60, 0x85, 0x8b, 0x20, 0x01, 0x54, 0x16, 0x92, 0x8c, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s6, s3);
            uint256_t const &s4 = top[-4];
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, s4, s5);
            uint256_t const &s7 = top[-7];
            auto const h30 = aot::sha3_any<traits>(ctx, gas, s6, s7);
            gas = ctx->gas_remaining;
            uint256_t const t1 = h30 + uint256_t{0x1ull};
            uint256_t const t2 = aot::sload<traits>(ctx, gas, t1);
            uint256_t const &s8 = top[-8];
            uint256_t const t3 = t2 & s8;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const m8 = s8;
            uint256_t const m3 = s3;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const m5 = s5;
            uint256_t const m6 = s6;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const m4 = s4;
            uint256_t const m7 = s7;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-10] = m9;
            top[-9] = m8;
            top[-8] = uint256_t{0x2ull};
            top[-2] = m3;
            top[-1] = uint256_t{0xbbd8b7ac0f8fce87ull, 0xb78bc508ddc0891full, 0xfe415f779a620a62ull, 0x9d9bd501d0657d7dull};
            top[0] = uint256_t{0x60ull};
            top[1] = m10;
            top[2] = uint256_t{0x34f0ull};
            top[3] = m5;
            top[4] = m6;
            top[5] = m2;
            top[6] = m4;
            top[7] = m3;
            top[8] = m8;
            top[9] = m7;
            top[10] = t3;
            top[11] = uint256_t{0x34fbull};
            top[12] = uint256_t{0x34b0ull};
            top[13] = m1;
            top[14] = m10;
            top += 14;
            MONAD_AOT_TAIL return b_383b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_34b0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x61, 0x67, 0x61, 0x85, 0x80, 0x61, 0x56}, 3, 6));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x61, 0x67, 0x61, 0x85, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[0] = m2;
            top[1] = uint256_t{0x34f5ull};
            top[2] = uint256_t{0x1bc16d674ec80000ull};
            top[3] = uint256_t{0x34c7ull};
            top[4] = m0;
            top[5] = m0;
            top += 5;
            MONAD_AOT_TAIL return b_383b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_34c7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x04, 0x93, 0x67, 0x9c, 0x85, 0x67, 0x8f, 0x97, 0x84, 0x61, 0x91, 0x61, 0x56}, 14, 6));
            if (MONAD_UNLIKELY(top - bottom < 14)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x04, 0x93, 0x67, 0x9c, 0x85, 0x67, 0x8f, 0x97, 0x84, 0x61, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::udiv(s0, s1);
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s13 = top[-13];
            uint256_t const m13 = s13;
            top[-13] = uint256_t{0xde0b6b3a7640000ull};
            top[-5] = uint256_t{0xde0b6b3a7640000ull};
            top[-1] = m5;
            top[0] = m13;
            top[1] = t1;
            top[2] = uint256_t{0x29a2241af62c0000ull};
            top[3] = uint256_t{0x34e9ull};
            top[4] = m5;
            top[5] = t1;
            top += 5;
            MONAD_AOT_TAIL return b_383b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_34e9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x04, 0x92, 0x61, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x04, 0x92, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::udiv(s0, s1);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-4] = t1;
            top[-1] = m4;
            top += -1;
            MONAD_AOT_TAIL return b_316b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_34f0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_316b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_34f5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x61, 0x56}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = m0;
            top[0] = m1;
            MONAD_AOT_TAIL return b_383b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_34fb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x04, 0x95, 0x61, 0x87, 0x61, 0x56}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x04, 0x95, 0x61, 0x87, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::udiv(s0, s1);
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[-7] = t1;
            top[-1] = m7;
            top[0] = uint256_t{0x3506ull};
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_3c78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3506(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x82, 0x52, 0x88, 0x86, 0x52, 0x60, 0x83, 0x83, 0x20, 0x01, 0x84, 0x61, 0x82, 0x54, 0x93, 0x82, 0x85, 0x16, 0x61, 0x56}, 9, 6));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x82, 0x52, 0x88, 0x86, 0x52, 0x60, 0x83, 0x83, 0x20, 0x01, 0x84, 0x61, 0x82, 0x54, 0x93, 0x82, 0x85, 0x16, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, s1, s4);
            uint256_t const &s5 = top[-5];
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, s5, s8);
            uint256_t const &s2 = top[-2];
            auto const h10 = aot::sha3_any<traits>(ctx, gas, s1, s2);
            gas = ctx->gas_remaining;
            uint256_t const t1 = h10 + uint256_t{0x1ull};
            uint256_t const t2 = aot::sload<traits>(ctx, gas, t1);
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = t2 & s3;
            uint256_t const m3 = s3;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t2;
            top[1] = t1;
            top[2] = m3;
            top[3] = uint256_t{0x3521ull};
            top[4] = m0;
            top[5] = t3;
            top += 5;
            MONAD_AOT_TAIL return b_3178<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3521(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x16, 0x7f, 0x80, 0x93, 0x16, 0x17, 0x90, 0x55, 0x61, 0x88, 0x61, 0x56}, 11, 1));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x16, 0x7f, 0x80, 0x93, 0x16, 0x17, 0x90, 0x55, 0x61, 0x88, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 & s1;
            uint256_t const &s3 = top[-3];
            uint256_t const t2 = s3 & uint256_t{0x0ull, 0x0ull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t3 = t2 | t1;
            uint256_t const &s2 = top[-2];
            aot::sstore<traits>(ctx, gas, s2, t3, (aot::gas_of<traits>({0x61, 0x88, 0x61, 0x56}) + 0));
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[-3] = uint256_t{0x0ull, 0x0ull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            top[-2] = uint256_t{0x3552ull};
            top[-1] = m10;
            top += -1;
            MONAD_AOT_TAIL return b_3c78<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3552(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x85, 0x83, 0x52, 0x89, 0x87, 0x52, 0x83, 0x83, 0x20, 0x91, 0x85, 0x61, 0x84, 0x54, 0x93, 0x82, 0x85, 0x16, 0x61, 0x56}, 10, 6));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x85, 0x83, 0x52, 0x89, 0x87, 0x52, 0x83, 0x83, 0x20, 0x91, 0x85, 0x61, 0x84, 0x54, 0x93, 0x82, 0x85, 0x16, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, s2, s5);
            uint256_t const &s6 = top[-6];
            uint256_t const &s9 = top[-9];
            aot::mstore<traits>(ctx, gas, s6, s9);
            uint256_t const &s3 = top[-3];
            auto const h9 = aot::sha3_any<traits>(ctx, gas, s2, s3);
            gas = ctx->gas_remaining;
            uint256_t const t1 = aot::sload<traits>(ctx, gas, h9);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = t1 & s4;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const m4 = s4;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = h9;
            top[0] = t1;
            top[1] = m1;
            top[2] = m4;
            top[3] = uint256_t{0x356bull};
            top[4] = m0;
            top[5] = t2;
            top += 5;
            MONAD_AOT_TAIL return b_3178<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_356b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x80, 0x97, 0x84, 0x82, 0x52, 0x80, 0x86, 0x52, 0x60, 0x83, 0x83, 0x20, 0x01, 0x54, 0x60, 0x1c, 0x99, 0x8a, 0x61, 0x57}, 14, 0));
            if (MONAD_UNLIKELY(top - bottom < 14)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x16, 0x91, 0x16, 0x17, 0x90, 0x55, 0x80, 0x97, 0x84, 0x82, 0x52, 0x80, 0x86, 0x52, 0x60, 0x83, 0x83, 0x20, 0x01, 0x54, 0x60, 0x1c, 0x99, 0x8a, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 & s1;
            uint256_t const &s3 = top[-3];
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s3 & s2;
            uint256_t const t3 = t2 | t1;
            uint256_t const &s4 = top[-4];
            aot::sstore<traits>(ctx, gas, s4, t3, (aot::gas_of<traits>({0x80, 0x97, 0x84, 0x82, 0x52, 0x80, 0x86, 0x52, 0x60, 0x83, 0x83, 0x20, 0x01, 0x54, 0x60, 0x1c, 0x99, 0x8a, 0x61, 0x57}) + 0));
            uint256_t const &s5 = top[-5];
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, s5, s8);
            uint256_t const &s9 = top[-9];
            uint256_t const &s12 = top[-12];
            aot::mstore<traits>(ctx, gas, s9, s12);
            uint256_t const &s6 = top[-6];
            auto const h18 = aot::sha3_any<traits>(ctx, gas, s5, s6);
            gas = ctx->gas_remaining;
            uint256_t const t4 = h18 + uint256_t{0x2ull};
            uint256_t const t5 = aot::sload<traits>(ctx, gas, t4);
            uint256_t const t6 = aot::shr_c<128>(t5);
            bool const j26 = aot::nonzero(t6);
            uint256_t const m5 = s5;
            uint256_t const m12 = s12;
            uint256_t const &s13 = top[-13];
            uint256_t const m13 = s13;
            top[-13] = t6;
            top[-12] = m5;
            top[-4] = m12;
            top[-3] = m13;
            top += -3;
            if (j26) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x35aa); }
            MONAD_AOT_TAIL return b_358a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_358a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x90, 0x51, 0x98, 0x89, 0x52, 0x50, 0x50, 0x50, 0x50, 0x50, 0x88, 0x84, 0x01, 0x52, 0x8a, 0x83, 0x01, 0x52, 0x50, 0xa2, 0x87, 0x96, 0x95, 0x38, 0x80, 0x61, 0x56}, 23, 0));
            if (MONAD_UNLIKELY(top - bottom < 23)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x90, 0x51, 0x98, 0x89, 0x52, 0x50, 0x50, 0x50, 0x50, 0x50, 0x88, 0x84, 0x01, 0x52, 0x8a, 0x83, 0x01, 0x52, 0x50, 0xa2, 0x87, 0x96, 0x95, 0x38, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const &s11 = top[-11];
            aot::mstore<traits>(ctx, gas, t1, s11);
            uint256_t const &s16 = top[-16];
            uint256_t const t2 = t1 + s16;
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, t2, s8);
            uint256_t const &s19 = top[-19];
            uint256_t const t3 = t1 + s19;
            uint256_t const &s9 = top[-9];
            aot::mstore<traits>(ctx, gas, t3, s9);
            uint256_t const &s12 = top[-12];
            uint256_t const &s13 = top[-13];
            uint256_t const &s14 = top[-14];
            aot::log2<traits>(ctx, gas, t1, s12, s13, s14);
            gas = ctx->gas_remaining;
            uint256_t const &s22 = top[-22];
            uint256_t const m22 = s22;
            uint256_t const &s21 = top[-21];
            uint256_t const m21 = s21;
            uint256_t const &s20 = top[-20];
            uint256_t const m20 = s20;
            top[-21] = m22;
            top[-20] = m21;
            top[-14] = m20;
            top[-13] = uint256_t{0x3d07ull};
            top[-12] = uint256_t{0x3d07ull};
            top += -12;
            MONAD_AOT_TAIL return b_33cf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3637(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x99, 0x50, 0x83, 0x81, 0x81, 0x3d, 0x83, 0x11, 0x61, 0x57}, 11, 4));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x99, 0x50, 0x83, 0x81, 0x81, 0x3d, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = aot::from_bool(t1 < s4);
            bool const j11 = aot::nonzero(t2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m4 = s4;
            top[-10] = m1;
            top[-1] = m0;
            top[0] = m4;
            top[1] = m0;
            top[2] = m4;
            top += 2;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3660); }
            MONAD_AOT_TAIL return b_3645<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3645(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            top[1] = uint256_t{0x364full};
            top[2] = m0;
            top[3] = m1;
            top += 3;
            MONAD_AOT_TAIL return b_2d0f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_364f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1bd0); }
            MONAD_AOT_TAIL return b_3658<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3658(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x51, 0x98, 0x60, 0x61, 0x56}, 10, 2));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x51, 0x98, 0x60, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[-9] = t1;
            top[0] = m9;
            top[1] = uint256_t{0x60ull};
            top += 1;
            MONAD_AOT_TAIL return b_345f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3671(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x90, 0x50, 0x56}, 9, 0));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x90, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint64_t const jt = aot::jump_offset(s7);
            top += -9;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_367c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x92, 0x91, 0x60, 0x93, 0x80, 0x85, 0x52, 0x60, 0x92, 0x60, 0x84, 0x52, 0x60, 0x86, 0x20, 0x73, 0x90, 0x81, 0x85, 0x16, 0x88, 0x52, 0x85, 0x52, 0x6f, 0x60, 0x60, 0x89, 0x20, 0x01, 0x54, 0x16, 0x15, 0x61, 0x57}, 4, 7));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x92, 0x91, 0x60, 0x93, 0x80, 0x85, 0x52, 0x60, 0x92, 0x60, 0x84, 0x52, 0x60, 0x86, 0x20, 0x73, 0x90, 0x81, 0x85, 0x16, 0x88, 0x52, 0x85, 0x52, 0x6f, 0x60, 0x60, 0x89, 0x20, 0x01, 0x54, 0x16, 0x15, 0x61, 0x57}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, s1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x2ull});
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s2 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t1);
            uint256_t const t3 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t4 = t3 + uint256_t{0x1ull};
            uint256_t const t5 = aot::sload<traits>(ctx, gas, t4);
            uint256_t const t6 = t5 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            bool const j36 = aot::nonzero(t7);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const m2 = s2;
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-3] = uint256_t{0x0ull};
            top[-2] = m3;
            top[-1] = uint256_t{0x20ull};
            top[0] = m2;
            top[1] = m1;
            top[2] = m0;
            top[3] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top += 3;
            if (j36) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3762); }
            MONAD_AOT_TAIL return b_36cd<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_36cd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x84, 0x60, 0x91, 0x60, 0x84, 0x01, 0x51, 0x16, 0x60, 0x51, 0x92, 0x83, 0x80, 0x92, 0x7f, 0x82, 0x52, 0x5a, 0xfa, 0x94, 0x85, 0x15, 0x61, 0x57}, 5, 7));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x84, 0x60, 0x91, 0x60, 0x84, 0x01, 0x51, 0x16, 0x60, 0x51, 0x92, 0x83, 0x80, 0x92, 0x7f, 0x82, 0x52, 0x5a, 0xfa, 0x94, 0x85, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x40ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s0 = top[0];
            uint256_t const t3 = t2 & s0;
            uint256_t const t4 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xa035b1fe00000000ull});
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x94, 0x85, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k18_3 = uint256_t{0x4ull};
            uint256_t const &s4 = top[-4];
            ctx->gas_remaining = gas;
            uint256_t r18;
            runtime::staticcall<traits>(ctx, &r18, &t5, &t3, &t4, &k18_3, &t4, &s4, (aot::gas_of<traits>({0x94, 0x85, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(r18));
            bool const j23 = aot::nonzero(t6);
            uint256_t const m4 = s4;
            top[-4] = r18;
            top[0] = t4;
            top[1] = m4;
            top += 1;
            if (j23) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3757); }
            MONAD_AOT_TAIL return b_370a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_370a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x87, 0x95, 0x61, 0x57}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x87, 0x95, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            bool const j3 = aot::nonzero(s5);
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[-5] = m7;
            if (j3) { MONAD_AOT_TAIL return b_3720<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3710<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3710(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x61, 0x94, 0x95, 0x50, 0x61, 0x56}, 8, 0));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x61, 0x94, 0x95, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-7] = m6;
            top[-6] = uint256_t{0x371dull};
            top += -2;
            MONAD_AOT_TAIL return b_376d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_371d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3720(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x80, 0x92, 0x95, 0x50, 0x81, 0x3d, 0x83, 0x11, 0x61, 0x57}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x80, 0x92, 0x95, 0x50, 0x81, 0x3d, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::from_bool(t1 < s0);
            bool const j11 = aot::nonzero(t2);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const m0 = s0;
            top[-5] = m2;
            top[-2] = m1;
            top[-1] = m0;
            top[0] = m1;
            top[1] = m0;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3750); }
            MONAD_AOT_TAIL return b_372e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_372e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            top[1] = uint256_t{0x3738ull};
            top[2] = m0;
            top[3] = m1;
            top += 3;
            MONAD_AOT_TAIL return b_2d0f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3738(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1bd0); }
            MONAD_AOT_TAIL return b_3741<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3741(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x94, 0x95, 0x50, 0x51, 0x92, 0x85, 0x94, 0x38, 0x61, 0x56}, 6, 3));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x94, 0x95, 0x50, 0x51, 0x92, 0x85, 0x94, 0x38, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-5] = m4;
            top[-3] = t1;
            top[0] = m3;
            top[1] = uint256_t{0x371dull};
            top[2] = uint256_t{0x3d07ull};
            top += 2;
            MONAD_AOT_TAIL return b_3710<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_376d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x6e, 0x61, 0x61, 0x94, 0x96, 0x60, 0x60, 0x67, 0x98, 0x60, 0x90, 0x8b, 0x82, 0x52, 0x60, 0x60, 0x52, 0x73, 0x83, 0x83, 0x20, 0x91, 0x16, 0x90, 0x81, 0x83, 0x52, 0x60, 0x52, 0x61, 0x6f, 0x8d, 0x81, 0x87, 0x87, 0x87, 0x20, 0x01, 0x54, 0x16, 0x90, 0x85, 0x52, 0x60, 0x60, 0x52, 0x86, 0x86, 0x86, 0x20, 0x01, 0x54, 0x91, 0x82, 0x8c, 0x1c, 0x92, 0x16, 0x90, 0x61, 0x56}, 4, 15));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1009)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x6e, 0x61, 0x61, 0x94, 0x96, 0x60, 0x60, 0x67, 0x98, 0x60, 0x90, 0x8b, 0x82, 0x52, 0x60, 0x60, 0x52, 0x73, 0x83, 0x83, 0x20, 0x91, 0x16, 0x90, 0x81, 0x83, 0x52, 0x60, 0x52, 0x61, 0x6f, 0x8d, 0x81, 0x87, 0x87, 0x87, 0x20, 0x01, 0x54, 0x16, 0x90, 0x85, 0x52, 0x60, 0x60, 0x52, 0x86, 0x86, 0x86, 0x20, 0x01, 0x54, 0x91, 0x82, 0x8c, 0x1c, 0x92, 0x16, 0x90, 0x61, 0x56}) + 36;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, s1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x2ull});
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s2 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t1);
            uint256_t const t3 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t4 = t3 + uint256_t{0x1ull};
            uint256_t const t5 = aot::sload<traits>(ctx, gas, t4);
            uint256_t const t6 = t5 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, s1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const t7 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t8 = t7 + uint256_t{0x1ull};
            uint256_t const t9 = aot::sload<traits>(ctx, gas, t8);
            uint256_t const t10 = aot::shr_c<128>(t9);
            uint256_t const t11 = t9 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            uint256_t const m1 = s1;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = m1;
            top[-2] = uint256_t{0xde0b6b3a7640000ull};
            top[-1] = uint256_t{0x381dull};
            top[1] = uint256_t{0x80ull};
            top[2] = uint256_t{0xb34b9f1000000000ull, 0xc097ce7bc90715ull, 0x0ull, 0x0ull};
            top[3] = uint256_t{0x3813ull};
            top[4] = m3;
            top[5] = uint256_t{0x1ull};
            top[6] = uint256_t{0x40ull};
            top[7] = uint256_t{0x0ull};
            top[8] = t2;
            top[9] = uint256_t{0x37f8ull};
            top[10] = t10;
            top[11] = t11;
            top[12] = t6;
            top += 12;
            MONAD_AOT_TAIL return b_3c55<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_37f8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x9b, 0x82, 0x52, 0x60, 0x60, 0x52, 0x82, 0x82, 0x20, 0x90, 0x82, 0x52, 0x60, 0x52, 0x20, 0x01, 0x54, 0x84, 0x1c, 0x61, 0x56}, 13, 1));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x9b, 0x82, 0x52, 0x60, 0x60, 0x52, 0x82, 0x82, 0x20, 0x90, 0x82, 0x52, 0x60, 0x52, 0x20, 0x01, 0x54, 0x84, 0x1c, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s12 = top[-12];
            aot::mstore<traits>(ctx, gas, s2, s12);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x2ull});
            uint256_t const &s3 = top[-3];
            auto const h9 = aot::sha3_any<traits>(ctx, gas, s2, s3);
            gas = ctx->gas_remaining;
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s2, s1);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, h9);
            auto const h15 = aot::sha3_any<traits>(ctx, gas, s2, s3);
            gas = ctx->gas_remaining;
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = h15 + s4;
            uint256_t const t2 = aot::sload<traits>(ctx, gas, t1);
            uint256_t const &s8 = top[-8];
            uint256_t const t3 = aot::shr(s8, t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-12] = m0;
            top[-4] = t3;
            top += -4;
            MONAD_AOT_TAIL return b_383b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3813(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x04, 0x91, 0x01, 0x51, 0x90, 0x61, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x04, 0x91, 0x01, 0x51, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::udiv(s0, s1);
            uint256_t const &s3 = top[-3];
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s3 + s2;
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            top[-3] = t3;
            top[-2] = t1;
            top += -2;
            MONAD_AOT_TAIL return b_383b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_381d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x04, 0x10, 0x15, 0x90, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x04, 0x10, 0x15, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::udiv(s0, s1);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = aot::from_bool(t1 < s2);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top[-3] = t3;
            top += -3;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3823(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x67, 0x81, 0x11, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x67, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xffffffffffffffffull} < s0);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a35); }
            MONAD_AOT_TAIL return b_3833<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3833(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_383b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x81, 0x02, 0x92, 0x91, 0x81, 0x15, 0x91, 0x84, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x81, 0x02, 0x92, 0x91, 0x81, 0x15, 0x91, 0x84, 0x04, 0x14, 0x17, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mul(s0, s1);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const t3 = aot::udiv(t1, s0);
            uint256_t const t4 = aot::from_bool(t3 == s1);
            uint256_t const t5 = t4 | t2;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j15 = aot::nonzero(t6);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[-1] = m2;
            top += -1;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_384d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_384d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_384e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x15, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s1));
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xdf4); }
            MONAD_AOT_TAIL return b_3855<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3855(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x04, 0x90, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x04, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::udiv(s0, s1);
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t1;
            top += -2;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3858(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x61, 0x91, 0x61, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x61, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = uint256_t{0x3862ull};
            top[0] = m1;
            top[1] = m0;
            top += 1;
            MONAD_AOT_TAIL return b_383b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3862(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x7f, 0x81, 0x01, 0x91, 0x81, 0x83, 0x11, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x7f, 0x81, 0x01, 0x91, 0x81, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t2 = aot::from_bool(s1 < t1);
            bool const j10 = aot::nonzero(t2);
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-1] = t1;
            top[0] = m1;
            top[1] = m0;
            top += 1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_388f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_388f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x92, 0x61, 0x91, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x92, 0x61, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = uint256_t{0x371dull};
            top[0] = uint256_t{0x7d4ull};
            top[1] = m2;
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_316b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_389b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x38a8ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_38a8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x7ull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x6e6f20636f646500ull});
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_38d4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x3d, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x3d, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j4 = aot::nonzero(t2);
            if (j4) { MONAD_AOT_TAIL return b_392d<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_38db<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_38db(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x90, 0x67, 0x82, 0x11, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x90, 0x67, 0x82, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j6 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top += 1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1a35); }
            MONAD_AOT_TAIL return b_38ec<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_38ec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x51, 0x91, 0x61, 0x60, 0x7f, 0x60, 0x84, 0x01, 0x16, 0x01, 0x84, 0x61, 0x56}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x51, 0x91, 0x61, 0x60, 0x7f, 0x60, 0x84, 0x01, 0x16, 0x01, 0x84, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s1 + uint256_t{0x1full};
            uint256_t const t3 = t2 & uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const t4 = t3 + uint256_t{0x20ull};
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[1] = m1;
            top[2] = uint256_t{0x3921ull};
            top[3] = t4;
            top[4] = t1;
            top += 4;
            MONAD_AOT_TAIL return b_2d0f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3921(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x52, 0x3d, 0x60, 0x60, 0x84, 0x01, 0x3e, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x52, 0x3d, 0x60, 0x60, 0x84, 0x01, 0x3e, 0x56}) + 0;
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
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_392d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x90, 0x56}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top[0] = uint256_t{0x60ull};
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3932(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x81, 0x60, 0x91, 0x03, 0x12, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x81, 0x60, 0x91, 0x03, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 - s0;
            uint256_t const t2 = aot::from_bool(slt(t1, uint256_t{0x20ull}));
            bool const j8 = aot::nonzero(t2);
            uint256_t const m0 = s0;
            top[-1] = m0;
            top += -1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_393e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_393e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x51, 0x80, 0x15, 0x15, 0x81, 0x03, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x51, 0x80, 0x15, 0x15, 0x81, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t4 = t1 - t3;
            bool const j7 = aot::nonzero(t4);
            top[0] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2c8); }
            MONAD_AOT_TAIL return b_3948<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3948(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_394a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x92, 0x60, 0x92, 0x83, 0x61, 0x61, 0x73, 0x83, 0x96, 0x16, 0x94, 0x61, 0x86, 0x3b, 0x15, 0x15, 0x61, 0x61, 0x56}, 3, 10));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x92, 0x60, 0x92, 0x83, 0x61, 0x61, 0x73, 0x83, 0x96, 0x16, 0x94, 0x61, 0x86, 0x3b, 0x15, 0x15, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            ctx->gas_remaining = gas;
            uint256_t r15;
            runtime::extcodesize<traits>(ctx, &r15, &t1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::from_bool(!aot::nonzero(r15));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = uint256_t{0x3a9dull};
            top[-1] = uint256_t{0x0ull};
            top[0] = uint256_t{0x0ull};
            top[1] = t1;
            top[2] = m1;
            top[3] = uint256_t{0x0ull};
            top[4] = uint256_t{0x39daull};
            top[5] = uint256_t{0x3a06ull};
            top[6] = m2;
            top[7] = uint256_t{0x3980ull};
            top[8] = t3;
            top[9] = uint256_t{0x249ull};
            top += 9;
            MONAD_AOT_TAIL return b_389b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3980(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x92, 0x83, 0x91, 0x60, 0x83, 0x01, 0x96, 0x7f, 0x88, 0x52, 0x60, 0x84, 0x01, 0x60, 0x90, 0x93, 0x92, 0x91, 0x93, 0x73, 0x60, 0x82, 0x01, 0x95, 0x16, 0x81, 0x52, 0x01, 0x52, 0x56}, 5, 8));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x92, 0x83, 0x91, 0x60, 0x83, 0x01, 0x96, 0x7f, 0x88, 0x52, 0x60, 0x84, 0x01, 0x60, 0x90, 0x93, 0x92, 0x91, 0x93, 0x73, 0x60, 0x82, 0x01, 0x95, 0x16, 0x81, 0x52, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x0ull, 0x0ull, 0x0ull, 0xa9059cbb00000000ull});
            uint256_t const t3 = t1 + uint256_t{0x24ull};
            uint256_t const t4 = t3 + uint256_t{0x40ull};
            uint256_t const &s4 = top[-4];
            uint256_t const t5 = s4 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            aot::mstore<traits>(ctx, gas, t3, t5);
            uint256_t const t6 = t3 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t6, s0);
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-4] = t2;
            top[-2] = t1;
            top[0] = t1;
            top[1] = t4;
            top += 1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_39da(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            MONAD_AOT_TAIL return b_2d0f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3a06(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x92, 0x5a, 0xf1, 0x61, 0x61, 0x61, 0x56}, 6, 1));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x92, 0x5a, 0xf1, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xf1, 0x61, 0x61, 0x61, 0x56}) + 0))};
            uint256_t const &s3 = top[-3];
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t const &s4 = top[-4];
            uint256_t const &s5 = top[-5];
            auto const c4 = aot::call<traits>(ctx, gas, t2, s3, s1, s2, t1, s4, s5, (aot::gas_of<traits>({0x61, 0x61, 0x61, 0x56}) + 0));
            gas = ctx->gas_remaining;
            top[-5] = c4;
            top[-4] = uint256_t{0x3a52ull};
            top[-3] = uint256_t{0x3a15ull};
            top += -3;
            MONAD_AOT_TAIL return b_38d4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3a15(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[0] = t1;
            top[1] = m2;
            top[2] = uint256_t{0x3a23ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3a23(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x61, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x11ull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x6400000000000000ull, 0x2072657665727465ull, 0x7472616e73666572ull});
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3a52(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x51, 0x90, 0x81, 0x15, 0x91, 0x82, 0x15, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x51, 0x90, 0x81, 0x15, 0x91, 0x82, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j10 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[0] = t2;
            top[1] = m0;
            top[2] = t1;
            top += 2;
            if (j10) { MONAD_AOT_TAIL return b_3a9f<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3a5f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3a5f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[-1] = m2;
            top[0] = uint256_t{0x3a6eull};
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3a6e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x61, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x17ull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x642066616c736500ull, 0x2072657475726e65ull, 0x7472616e73666572ull});
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3a9d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 15623)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3a9f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x92, 0x50, 0x60, 0x80, 0x91, 0x83, 0x01, 0x01, 0x91, 0x01, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x92, 0x50, 0x60, 0x80, 0x91, 0x83, 0x01, 0x01, 0x91, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 + s0;
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            uint256_t const t3 = s1 + uint256_t{0x20ull};
            top[-2] = uint256_t{0x3ab2ull};
            top[-1] = t2;
            top[0] = t3;
            MONAD_AOT_TAIL return b_3932<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3ab2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x38, 0x80, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x38, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x3d07ull};
            top[2] = uint256_t{0x3d07ull};
            top += 2;
            MONAD_AOT_TAIL return b_3a5f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3ab9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x92, 0x91, 0x83, 0x80, 0x93, 0x61, 0x96, 0x73, 0x80, 0x95, 0x16, 0x94, 0x61, 0x86, 0x3b, 0x15, 0x15, 0x61, 0x61, 0x56}, 4, 9));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x92, 0x91, 0x83, 0x80, 0x93, 0x61, 0x96, 0x73, 0x80, 0x95, 0x16, 0x94, 0x61, 0x86, 0x3b, 0x15, 0x15, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 & uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            ctx->gas_remaining = gas;
            uint256_t r16;
            runtime::extcodesize<traits>(ctx, &r16, &t1);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::from_bool(!aot::nonzero(r16));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = uint256_t{0x3a9dull};
            top[-2] = uint256_t{0x0ull};
            top[-1] = uint256_t{0x0ull};
            top[0] = t1;
            top[1] = m1;
            top[2] = uint256_t{0x0ull};
            top[3] = m2;
            top[4] = m3;
            top[5] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull};
            top[6] = uint256_t{0x3aecull};
            top[7] = t3;
            top[8] = uint256_t{0x249ull};
            top += 8;
            MONAD_AOT_TAIL return b_389b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3aec(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x92, 0x81, 0x60, 0x85, 0x01, 0x96, 0x7f, 0x88, 0x52, 0x16, 0x60, 0x85, 0x01, 0x52, 0x16, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x61, 0x81, 0x61, 0x56}, 5, 5));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x92, 0x81, 0x60, 0x85, 0x01, 0x96, 0x7f, 0x88, 0x52, 0x16, 0x60, 0x85, 0x01, 0x52, 0x16, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x60, 0x81, 0x52, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x23b872dd00000000ull});
            uint256_t const &s4 = top[-4];
            uint256_t const &s0 = top[0];
            uint256_t const t3 = s4 & s0;
            uint256_t const t4 = t1 + uint256_t{0x24ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const &s2 = top[-2];
            uint256_t const t5 = s2 & s0;
            uint256_t const t6 = t1 + uint256_t{0x44ull};
            aot::mstore<traits>(ctx, gas, t6, t5);
            uint256_t const t7 = t1 + uint256_t{0x64ull};
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t7, s1);
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x64ull});
            top[-4] = t2;
            top[-2] = t1;
            top[-1] = uint256_t{0x3b37ull};
            top[0] = t1;
            MONAD_AOT_TAIL return b_2cd7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3b37(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x51, 0x92, 0x5a, 0xf1, 0x61, 0x61, 0x61, 0x56}, 6, 1));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x51, 0x92, 0x5a, 0xf1, 0x61, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xf1, 0x61, 0x61, 0x61, 0x56}) + 0))};
            uint256_t const &s3 = top[-3];
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t const &s4 = top[-4];
            uint256_t const &s5 = top[-5];
            auto const c4 = aot::call<traits>(ctx, gas, t2, s3, s1, s2, t1, s4, s5, (aot::gas_of<traits>({0x61, 0x61, 0x61, 0x56}) + 0));
            gas = ctx->gas_remaining;
            top[-5] = c4;
            top[-4] = uint256_t{0x3b83ull};
            top[-3] = uint256_t{0x3b46ull};
            top += -3;
            MONAD_AOT_TAIL return b_38d4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3b46(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[0] = t1;
            top[1] = m2;
            top[2] = uint256_t{0x3b54ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3b54(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x61, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x15ull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x6572746564000000ull, 0x46726f6d20726576ull, 0x7472616e73666572ull});
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3b83(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x51, 0x90, 0x81, 0x15, 0x91, 0x82, 0x15, 0x61, 0x57}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x51, 0x90, 0x81, 0x15, 0x91, 0x82, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j10 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[0] = t2;
            top[1] = m0;
            top[2] = t1;
            top += 2;
            if (j10) { MONAD_AOT_TAIL return b_3bce<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_3b90<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3b90(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[-1] = m2;
            top[0] = uint256_t{0x3b9full};
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3b9f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x61, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x1bull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x6c73650000000000ull, 0x75726e6564206661ull, 0x46726f6d20726574ull, 0x7472616e73666572ull});
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3bce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x92, 0x50, 0x60, 0x80, 0x91, 0x83, 0x01, 0x01, 0x91, 0x01, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x92, 0x50, 0x60, 0x80, 0x91, 0x83, 0x01, 0x01, 0x91, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 + s0;
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            uint256_t const t3 = s1 + uint256_t{0x20ull};
            top[-2] = uint256_t{0x3be1ull};
            top[-1] = t2;
            top[0] = t3;
            MONAD_AOT_TAIL return b_3932<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3be1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x38, 0x80, 0x61, 0x56}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x38, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x3d07ull};
            top[2] = uint256_t{0x3d07ull};
            top += 2;
            MONAD_AOT_TAIL return b_3b90<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3be8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x62, 0x83, 0x01, 0x80, 0x93, 0x11, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x62, 0x83, 0x01, 0x80, 0x93, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0xf4240ull};
            uint256_t const t2 = aot::from_bool(t1 < s2);
            bool const j8 = aot::nonzero(t2);
            top[-2] = t1;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_3bf6<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3bf6(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x82, 0x01, 0x80, 0x92, 0x11, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x82, 0x01, 0x80, 0x92, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x1ull};
            uint256_t const t2 = aot::from_bool(t1 < s1);
            bool const j7 = aot::nonzero(t2);
            top[-1] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_3c01<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c01(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x92, 0x61, 0x91, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x92, 0x61, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = uint256_t{0x371dull};
            top[0] = uint256_t{0x7d4ull};
            top[1] = m2;
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_383b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3c0d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x01, 0x92, 0x91, 0x83, 0x10, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x01, 0x92, 0x91, 0x83, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x1ull};
            uint256_t const t2 = aot::from_bool(t1 < s1);
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[-1] = m2;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_3c1a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c1a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x62, 0x82, 0x01, 0x80, 0x92, 0x11, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x62, 0x82, 0x01, 0x80, 0x92, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0xf4240ull};
            uint256_t const t2 = aot::from_bool(t1 < s1);
            bool const j7 = aot::nonzero(t2);
            top[-1] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_3c27<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c27(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x92, 0x61, 0x91, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x92, 0x61, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = uint256_t{0x371dull};
            top[0] = uint256_t{0x7d4ull};
            top[1] = m2;
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_383b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3c33(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x62, 0x81, 0x01, 0x80, 0x91, 0x11, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x62, 0x81, 0x01, 0x80, 0x91, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0xf4240ull};
            uint256_t const t2 = aot::from_bool(t1 < s2);
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-2] = m0;
            top[0] = t1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_3c42<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c42(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x82, 0x01, 0x80, 0x92, 0x11, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x82, 0x01, 0x80, 0x92, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x1ull};
            uint256_t const t2 = aot::from_bool(t1 < s1);
            bool const j7 = aot::nonzero(t2);
            top[-1] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_3c4d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c4d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x92, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x92, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = uint256_t{0x371dull};
            top[1] = m2;
            top += 1;
            MONAD_AOT_TAIL return b_3858<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3c55(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x90, 0x60, 0x81, 0x01, 0x80, 0x91, 0x11, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x90, 0x60, 0x81, 0x01, 0x80, 0x91, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0x1ull};
            uint256_t const t2 = aot::from_bool(t1 < s1);
            bool const j10 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[-1] = m2;
            top[0] = t1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_3c63<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c63(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x62, 0x82, 0x01, 0x80, 0x92, 0x11, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x62, 0x82, 0x01, 0x80, 0x92, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s1 + uint256_t{0xf4240ull};
            uint256_t const t2 = aot::from_bool(t1 < s1);
            bool const j7 = aot::nonzero(t2);
            top[-1] = t1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xccd); }
            MONAD_AOT_TAIL return b_3c70<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_3c70(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x92, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x92, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = uint256_t{0x371dull};
            top[1] = m2;
            top += 1;
            MONAD_AOT_TAIL return b_3858<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3c78(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x3c85ull};
            top[3] = t1;
            top += 3;
            MONAD_AOT_TAIL return b_2cf3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3c85(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x61, 0x6f, 0x92, 0x83, 0x83, 0x11, 0x15, 0x61, 0x56}, 2, 4));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x61, 0x6f, 0x92, 0x83, 0x83, 0x11, 0x15, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x14ull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x0ull, 0x6564656400000000ull, 0x3132382065786365ull, 0x6d61782075696e74ull});
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull} < s0);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const m1 = s1;
            top[-1] = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0x0ull, 0x0ull};
            top[1] = uint256_t{0x3ccdull};
            top[2] = m1;
            top[3] = t3;
            top += 3;
            MONAD_AOT_TAIL return b_2f41<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_3ccd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x16, 0x90, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x16, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 & s1;
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t1;
            top += -2;
            if (MONAD_LIKELY(jt < 15623)) {
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

    template void c_fa259fa317198f88::run<EvmTraits<MONAD_ETH_OSAKA>>(
        void *, Context *, interpreter::Intercode const *, uint256_t *, void *);
}
