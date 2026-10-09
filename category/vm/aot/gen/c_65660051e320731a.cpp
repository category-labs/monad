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

// Written by aotgen.py from the code whose keccak is 65660051e320731a70b9ddcd5ec9fd4f565cf85e2f6caf0eb71589fb544b9996: not to be edited.

#include <category/vm/aot/ops.hpp>
#include <category/vm/interpreter/execute.hpp>
#include <category/vm/interpreter/intercode.hpp>

#define MONAD_AOT_TAIL __attribute__((musttail))

namespace monad::vm::aot
{
    using runtime::Context;
    using runtime::StatusCode;

    // 1780 bytes, keccak 65660051e320731a70b9ddcd5ec9fd4f565cf85e2f6caf0eb71589fb544b9996
    namespace c_65660051e320731a
    {
        template <Traits traits>
        using Block = void (*)(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        [[gnu::noinline]] void b_0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_41(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_57(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_5c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_64(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_68(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_cd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_cf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_db(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_140(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_142(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_186(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_188(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_18e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_19a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1c4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ee(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1ef(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2aa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2ae(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2c2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2d8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2f0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_2f4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_301(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_309(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_315(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_321(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_32d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_32e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_346(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_419(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_41d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_428(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_431(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_443(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_447(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_45f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_463(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_468(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_474(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_49c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_49d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4c7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_4c8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_550(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_554(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_55f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_568(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_57a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_57e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_596(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_59a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_5a7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_5b0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_5b8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_5c4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_5d0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_5d1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_614(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_615(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_63e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_647(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_655(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_679(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6b5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_6be(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_6c0(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        void bad(Context *const ctx, uint256_t const *, uint256_t *, int64_t)
        {
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        inline constexpr Block<traits> jump_table[1780] = {
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_57<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_5c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_68<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_cd<traits>, &bad<traits>, &b_cf<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_db<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_140<traits>, &bad<traits>, &b_142<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_186<traits>, &bad<traits>, &b_188<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_18e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1c4<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1ef<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2ae<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2c2<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_2d8<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_2f4<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_301<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_309<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_315<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_32e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_346<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_41d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_431<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_447<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_463<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_468<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_49d<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_4c8<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_554<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_568<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_57e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_59a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_5a7<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_5b0<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_5b8<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_5d1<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_615<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_647<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_655<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_6be<traits>, &bad<traits>,
            &b_6c0<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
        };

        template <Traits traits>
        [[gnu::noinline]] void b_0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x52, 0x60, 0x36, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x52, 0x60, 0x36, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, uint256_t{0x80ull});
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x4ull});
            bool const j7 = aot::nonzero(t2);
            if (j7) { MONAD_AOT_TAIL return b_57<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x7c, 0x90, 0x04, 0x63, 0x16, 0x80, 0x63, 0x14, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x7c, 0x90, 0x04, 0x63, 0x16, 0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x0ull});
            uint256_t const t2 = aot::shr_c<224>(t1);
            uint256_t const t3 = uint256_t{0xffffffffull} & t2;
            uint256_t const t4 = aot::from_bool(uint256_t{0x51ba162cull} == t3);
            bool const j11 = aot::nonzero(t4);
            top[1] = t3;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return b_5c<traits>(ctx, bottom, top, gas); }
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
            uint256_t const t1 = aot::from_bool(uint256_t{0xc73a2d60ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_cf<traits>(ctx, bottom, top, gas); }
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
            uint256_t const t1 = aot::from_bool(uint256_t{0xe63d38edull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return b_142<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_57<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_57(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_5c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x80, 0x15, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j5 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j5) { MONAD_AOT_TAIL return b_68<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_64<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_64(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_68(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x61, 0x60, 0x80, 0x36, 0x03, 0x81, 0x01, 0x90, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x92, 0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x82, 0x01, 0x80, 0x35, 0x90, 0x60, 0x01, 0x91, 0x90, 0x91, 0x92, 0x93, 0x91, 0x92, 0x93, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x82, 0x01, 0x80, 0x35, 0x90, 0x60, 0x01, 0x91, 0x90, 0x91, 0x92, 0x93, 0x91, 0x92, 0x93, 0x90, 0x50, 0x50, 0x50, 0x61, 0x56}, 1, 9));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x61, 0x60, 0x80, 0x36, 0x03, 0x81, 0x01, 0x90, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x92, 0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x82, 0x01, 0x80, 0x35, 0x90, 0x60, 0x01, 0x91, 0x90, 0x91, 0x92, 0x93, 0x91, 0x92, 0x93, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x82, 0x01, 0x80, 0x35, 0x90, 0x60, 0x01, 0x91, 0x90, 0x91, 0x92, 0x93, 0x91, 0x92, 0x93, 0x90, 0x50, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 - uint256_t{0x4ull};
            uint256_t const t3 = uint256_t{0x4ull} + t2;
            uint256_t const t4 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t5 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t4;
            uint256_t const t6 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t7 = uint256_t{0x4ull} + t6;
            uint256_t const t8 = aot::calldataload(ctx, t7);
            uint256_t const t9 = uint256_t{0x20ull} + t7;
            uint256_t const t10 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t11 = uint256_t{0x4ull} + t10;
            uint256_t const t12 = aot::calldataload(ctx, t11);
            uint256_t const t13 = uint256_t{0x20ull} + t11;
            top[0] = uint256_t{0xcdull};
            top[1] = t5;
            top[2] = t9;
            top[3] = t8;
            top[4] = t13;
            top[5] = t12;
            top += 5;
            MONAD_AOT_TAIL return b_188<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_cd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x00}, 0, 0));
            gas -= aot::gas_of<traits>({0x5b, 0x00}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::stop(ctx, gas);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_cf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x80, 0x15, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j5 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j5) { MONAD_AOT_TAIL return b_db<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_d7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_db(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x61, 0x60, 0x80, 0x36, 0x03, 0x81, 0x01, 0x90, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x92, 0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x82, 0x01, 0x80, 0x35, 0x90, 0x60, 0x01, 0x91, 0x90, 0x91, 0x92, 0x93, 0x91, 0x92, 0x93, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x82, 0x01, 0x80, 0x35, 0x90, 0x60, 0x01, 0x91, 0x90, 0x91, 0x92, 0x93, 0x91, 0x92, 0x93, 0x90, 0x50, 0x50, 0x50, 0x61, 0x56}, 1, 9));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x61, 0x60, 0x80, 0x36, 0x03, 0x81, 0x01, 0x90, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x92, 0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x82, 0x01, 0x80, 0x35, 0x90, 0x60, 0x01, 0x91, 0x90, 0x91, 0x92, 0x93, 0x91, 0x92, 0x93, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x82, 0x01, 0x80, 0x35, 0x90, 0x60, 0x01, 0x91, 0x90, 0x91, 0x92, 0x93, 0x91, 0x92, 0x93, 0x90, 0x50, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 - uint256_t{0x4ull};
            uint256_t const t3 = uint256_t{0x4ull} + t2;
            uint256_t const t4 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t5 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t4;
            uint256_t const t6 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t7 = uint256_t{0x4ull} + t6;
            uint256_t const t8 = aot::calldataload(ctx, t7);
            uint256_t const t9 = uint256_t{0x20ull} + t7;
            uint256_t const t10 = aot::calldataload(ctx, uint256_t{0x44ull});
            uint256_t const t11 = uint256_t{0x4ull} + t10;
            uint256_t const t12 = aot::calldataload(ctx, t11);
            uint256_t const t13 = uint256_t{0x20ull} + t11;
            top[0] = uint256_t{0x140ull};
            top[1] = t5;
            top[2] = t9;
            top[3] = t8;
            top[4] = t13;
            top[5] = t12;
            top += 5;
            MONAD_AOT_TAIL return b_309<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_140(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x00}, 0, 0));
            gas -= aot::gas_of<traits>({0x5b, 0x00}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::stop(ctx, gas);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_142(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x80, 0x36, 0x03, 0x81, 0x01, 0x90, 0x80, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x82, 0x01, 0x80, 0x35, 0x90, 0x60, 0x01, 0x91, 0x90, 0x91, 0x92, 0x93, 0x91, 0x92, 0x93, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x82, 0x01, 0x80, 0x35, 0x90, 0x60, 0x01, 0x91, 0x90, 0x91, 0x92, 0x93, 0x91, 0x92, 0x93, 0x90, 0x50, 0x50, 0x50, 0x61, 0x56}, 0, 9));
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x80, 0x36, 0x03, 0x81, 0x01, 0x90, 0x80, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x82, 0x01, 0x80, 0x35, 0x90, 0x60, 0x01, 0x91, 0x90, 0x91, 0x92, 0x93, 0x91, 0x92, 0x93, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x82, 0x01, 0x80, 0x35, 0x90, 0x60, 0x01, 0x91, 0x90, 0x91, 0x92, 0x93, 0x91, 0x92, 0x93, 0x90, 0x50, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = t1 - uint256_t{0x4ull};
            uint256_t const t3 = uint256_t{0x4ull} + t2;
            uint256_t const t4 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t5 = uint256_t{0x4ull} + t4;
            uint256_t const t6 = aot::calldataload(ctx, t5);
            uint256_t const t7 = uint256_t{0x20ull} + t5;
            uint256_t const t8 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t9 = uint256_t{0x4ull} + t8;
            uint256_t const t10 = aot::calldataload(ctx, t9);
            uint256_t const t11 = uint256_t{0x20ull} + t9;
            top[1] = uint256_t{0x186ull};
            top[2] = t7;
            top[3] = t6;
            top[4] = t11;
            top[5] = t10;
            top += 5;
            MONAD_AOT_TAIL return b_5b0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_186(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x00}, 0, 0));
            gas -= aot::gas_of<traits>({0x5b, 0x00}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::stop(ctx, gas);
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_188(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x80, 0x90, 0x50}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x80, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top += 1;
            MONAD_AOT_TAIL return b_18e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_18e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x84, 0x90, 0x50, 0x81, 0x10, 0x15, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x84, 0x90, 0x50, 0x81, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::from_bool(s0 < s3);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            if (j9) { MONAD_AOT_TAIL return b_301<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_19a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_19a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x85, 0x73, 0x16, 0x63, 0x33, 0x87, 0x87, 0x85, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}, 6, 8));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x85, 0x73, 0x16, 0x63, 0x33, 0x87, 0x87, 0x85, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s5;
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = aot::from_bool(s0 < s3);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            bool const j14 = aot::nonzero(t5);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const m3 = s3;
            uint256_t const m0 = s0;
            top[1] = t1;
            top[2] = uint256_t{0x23b872ddull};
            top[3] = t2;
            top[4] = m4;
            top[5] = m3;
            top[6] = m0;
            top += 6;
            if (j14) { MONAD_AOT_TAIL return b_1c4<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1c3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1c3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0xfe}, 0, 0));
            static_assert(!aot::is_known<traits>(0xfe));
            gas -= aot::gas_of<traits>({0xfe}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1c4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x73, 0x16, 0x86, 0x86, 0x86, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}, 9, 3));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x73, 0x16, 0x86, 0x86, 0x86, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = t1 + s2;
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const t4 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t3;
            uint256_t const &s6 = top[-6];
            uint256_t const &s7 = top[-7];
            uint256_t const t5 = aot::from_bool(s6 < s7);
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            bool const j18 = aot::nonzero(t7);
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const m7 = s7;
            uint256_t const m6 = s6;
            top[-2] = t4;
            top[-1] = m8;
            top[0] = m7;
            top[1] = m6;
            top += 1;
            if (j18) { MONAD_AOT_TAIL return b_1ef<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_1ee<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ee(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0xfe}, 0, 0));
            static_assert(!aot::is_known<traits>(0xfe));
            gas -= aot::gas_of<traits>({0xfe}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1ef(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x60, 0x51, 0x84, 0x63, 0x16, 0x7c, 0x02, 0x81, 0x52, 0x60, 0x01, 0x80, 0x84, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x83, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x82, 0x81, 0x52, 0x60, 0x01, 0x93, 0x50, 0x50, 0x50, 0x50, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x60, 0x87, 0x80, 0x3b, 0x15, 0x80, 0x15, 0x61, 0x57}, 7, 5));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x60, 0x51, 0x84, 0x63, 0x16, 0x7c, 0x02, 0x81, 0x52, 0x60, 0x01, 0x80, 0x84, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x83, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x82, 0x81, 0x52, 0x60, 0x01, 0x93, 0x50, 0x50, 0x50, 0x50, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x60, 0x87, 0x80, 0x3b, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = t1 + s2;
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const t4 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s5 = top[-5];
            uint256_t const t5 = uint256_t{0xffffffffull} & s5;
            uint256_t const t6 = aot::shl_c<224>(t5);
            aot::mstore<traits>(ctx, gas, t4, t6);
            uint256_t const t7 = uint256_t{0x4ull} + t4;
            uint256_t const &s4 = top[-4];
            uint256_t const t8 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s4;
            uint256_t const t9 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t8;
            aot::mstore<traits>(ctx, gas, t7, t9);
            uint256_t const t10 = uint256_t{0x20ull} + t7;
            uint256_t const &s3 = top[-3];
            uint256_t const t11 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s3;
            uint256_t const t12 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t11;
            aot::mstore<traits>(ctx, gas, t10, t12);
            uint256_t const t13 = uint256_t{0x20ull} + t10;
            aot::mstore<traits>(ctx, gas, t13, t3);
            uint256_t const t14 = uint256_t{0x20ull} + t13;
            uint256_t const t15 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t16 = t14 - t15;
            uint256_t const &s6 = top[-6];
            ctx->gas_remaining = gas;
            uint256_t r57;
            runtime::extcodesize<traits>(ctx, &r57, &s6);
            gas = ctx->gas_remaining;
            uint256_t const t17 = aot::from_bool(!aot::nonzero(r57));
            uint256_t const t18 = aot::from_bool(!aot::nonzero(t17));
            bool const j62 = aot::nonzero(t18);
            uint256_t const m6 = s6;
            top[-4] = t14;
            top[-3] = uint256_t{0x20ull};
            top[-2] = t15;
            top[-1] = t16;
            top[0] = t15;
            top[1] = uint256_t{0x0ull};
            top[2] = m6;
            top[3] = t17;
            top += 3;
            if (j62) { MONAD_AOT_TAIL return b_2ae<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2aa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2aa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2ae(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j8) { MONAD_AOT_TAIL return b_2c2<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2b9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2b9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x60, 0x80, 0x3e, 0x3d, 0x60, 0xfd}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x60, 0x80, 0x3e, 0x3d, 0x60, 0xfd}) + 0;
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
        [[gnu::noinline]] void b_2c2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x60, 0x51, 0x3d, 0x60, 0x81, 0x10, 0x15, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x60, 0x51, 0x3d, 0x60, 0x81, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t3 = aot::from_bool(t2 < uint256_t{0x20ull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j13 = aot::nonzero(t4);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j13) { MONAD_AOT_TAIL return b_2d8<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2d4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2d8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x01, 0x90, 0x80, 0x80, 0x51, 0x90, 0x60, 0x01, 0x90, 0x92, 0x91, 0x90, 0x50, 0x50, 0x50, 0x15, 0x15, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x01, 0x90, 0x80, 0x80, 0x51, 0x90, 0x60, 0x01, 0x90, 0x92, 0x91, 0x90, 0x50, 0x50, 0x50, 0x15, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 + s0;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const t3 = uint256_t{0x20ull} + s1;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            bool const j20 = aot::nonzero(t5);
            top += -2;
            if (j20) { MONAD_AOT_TAIL return b_2f4<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_2f0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2f0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_2f4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x80, 0x60, 0x01, 0x91, 0x50, 0x50, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x80, 0x60, 0x01, 0x91, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x1ull} + s0;
            top[0] = t1;
            MONAD_AOT_TAIL return b_18e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_301(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint64_t const jt = aot::jump_offset(s6);
            top += -7;
            if (MONAD_LIKELY(jt < 1780)) {
                MONAD_AOT_TAIL return jump_table<traits>[jt](ctx, bottom, top, gas);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_309(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x80, 0x60, 0x91, 0x50, 0x60, 0x90, 0x50}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x80, 0x60, 0x91, 0x50, 0x60, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_315<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_315(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x85, 0x85, 0x90, 0x50, 0x81, 0x10, 0x15, 0x61, 0x57}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x85, 0x85, 0x90, 0x50, 0x81, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::from_bool(s0 < s4);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            if (j9) { MONAD_AOT_TAIL return b_346<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_321<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_321(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x83, 0x83, 0x82, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x83, 0x83, 0x82, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(s0 < s2);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j9 = aot::nonzero(t3);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const m2 = s2;
            uint256_t const m0 = s0;
            top[1] = m3;
            top[2] = m2;
            top[3] = m0;
            top += 3;
            if (j9) { MONAD_AOT_TAIL return b_32e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_32d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_32d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0xfe}, 0, 0));
            static_assert(!aot::is_known<traits>(0xfe));
            gas -= aot::gas_of<traits>({0xfe}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_32e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x82, 0x01, 0x91, 0x50, 0x80, 0x80, 0x60, 0x01, 0x91, 0x50, 0x50, 0x61, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x82, 0x01, 0x91, 0x50, 0x80, 0x80, 0x60, 0x01, 0x91, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = t1 + s2;
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const &s4 = top[-4];
            uint256_t const t4 = s4 + t3;
            uint256_t const &s3 = top[-3];
            uint256_t const t5 = uint256_t{0x1ull} + s3;
            top[-4] = t4;
            top[-3] = t5;
            top += -3;
            MONAD_AOT_TAIL return b_315<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_346(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x86, 0x73, 0x16, 0x63, 0x33, 0x30, 0x85, 0x60, 0x51, 0x84, 0x63, 0x16, 0x7c, 0x02, 0x81, 0x52, 0x60, 0x01, 0x80, 0x84, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x83, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x82, 0x81, 0x52, 0x60, 0x01, 0x93, 0x50, 0x50, 0x50, 0x50, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x60, 0x87, 0x80, 0x3b, 0x15, 0x80, 0x15, 0x61, 0x57}, 7, 12));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1012)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x86, 0x73, 0x16, 0x63, 0x33, 0x30, 0x85, 0x60, 0x51, 0x84, 0x63, 0x16, 0x7c, 0x02, 0x81, 0x52, 0x60, 0x01, 0x80, 0x84, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x83, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x82, 0x81, 0x52, 0x60, 0x01, 0x93, 0x50, 0x50, 0x50, 0x50, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x60, 0x87, 0x80, 0x3b, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s6;
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t3 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t4 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x0ull, 0x0ull, 0x0ull, 0x23b872dd00000000ull});
            uint256_t const t5 = uint256_t{0x4ull} + t4;
            uint256_t const t6 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t2;
            uint256_t const t7 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t6;
            aot::mstore<traits>(ctx, gas, t5, t7);
            uint256_t const t8 = uint256_t{0x20ull} + t5;
            uint256_t const t9 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t3;
            uint256_t const t10 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t9;
            aot::mstore<traits>(ctx, gas, t8, t10);
            uint256_t const t11 = uint256_t{0x20ull} + t8;
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t11, s1);
            uint256_t const t12 = uint256_t{0x20ull} + t11;
            uint256_t const t13 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t14 = t12 - t13;
            ctx->gas_remaining = gas;
            uint256_t r58;
            runtime::extcodesize<traits>(ctx, &r58, &t1);
            gas = ctx->gas_remaining;
            uint256_t const t15 = aot::from_bool(!aot::nonzero(r58));
            uint256_t const t16 = aot::from_bool(!aot::nonzero(t15));
            bool const j63 = aot::nonzero(t16);
            top[1] = t1;
            top[2] = uint256_t{0x23b872ddull};
            top[3] = t12;
            top[4] = uint256_t{0x20ull};
            top[5] = t13;
            top[6] = t14;
            top[7] = t13;
            top[8] = uint256_t{0x0ull};
            top[9] = t1;
            top[10] = t15;
            top += 10;
            if (j63) { MONAD_AOT_TAIL return b_41d<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_419<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_419(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_41d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j8) { MONAD_AOT_TAIL return b_431<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_428<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_428(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x60, 0x80, 0x3e, 0x3d, 0x60, 0xfd}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x60, 0x80, 0x3e, 0x3d, 0x60, 0xfd}) + 0;
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
        [[gnu::noinline]] void b_431(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x60, 0x51, 0x3d, 0x60, 0x81, 0x10, 0x15, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x60, 0x51, 0x3d, 0x60, 0x81, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t3 = aot::from_bool(t2 < uint256_t{0x20ull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j13 = aot::nonzero(t4);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j13) { MONAD_AOT_TAIL return b_447<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_443<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_443(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_447(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x01, 0x90, 0x80, 0x80, 0x51, 0x90, 0x60, 0x01, 0x90, 0x92, 0x91, 0x90, 0x50, 0x50, 0x50, 0x15, 0x15, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x01, 0x90, 0x80, 0x80, 0x51, 0x90, 0x60, 0x01, 0x90, 0x92, 0x91, 0x90, 0x50, 0x50, 0x50, 0x15, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 + s0;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const t3 = uint256_t{0x20ull} + s1;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            bool const j20 = aot::nonzero(t5);
            top += -2;
            if (j20) { MONAD_AOT_TAIL return b_463<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_45f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_45f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_463(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x90, 0x50}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x90, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[0] = uint256_t{0x0ull};
            MONAD_AOT_TAIL return b_468<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_468(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x85, 0x85, 0x90, 0x50, 0x81, 0x10, 0x15, 0x61, 0x57}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x85, 0x85, 0x90, 0x50, 0x81, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::from_bool(s0 < s4);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            if (j9) { MONAD_AOT_TAIL return b_5a7<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_474<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_474(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x86, 0x73, 0x16, 0x63, 0x87, 0x87, 0x84, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}, 7, 7));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x86, 0x73, 0x16, 0x63, 0x87, 0x87, 0x84, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s6;
            uint256_t const &s0 = top[0];
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = aot::from_bool(s0 < s4);
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j13 = aot::nonzero(t4);
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const m4 = s4;
            uint256_t const m0 = s0;
            top[1] = t1;
            top[2] = uint256_t{0xa9059cbbull};
            top[3] = m5;
            top[4] = m4;
            top[5] = m0;
            top += 5;
            if (j13) { MONAD_AOT_TAIL return b_49d<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_49c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_49c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0xfe}, 0, 0));
            static_assert(!aot::is_known<traits>(0xfe));
            gas -= aot::gas_of<traits>({0xfe}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_49d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x73, 0x16, 0x86, 0x86, 0x85, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}, 9, 3));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x73, 0x16, 0x86, 0x86, 0x85, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = t1 + s2;
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const t4 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t3;
            uint256_t const &s5 = top[-5];
            uint256_t const &s7 = top[-7];
            uint256_t const t5 = aot::from_bool(s5 < s7);
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            bool const j18 = aot::nonzero(t7);
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const m7 = s7;
            uint256_t const m5 = s5;
            top[-2] = t4;
            top[-1] = m8;
            top[0] = m7;
            top[1] = m5;
            top += 1;
            if (j18) { MONAD_AOT_TAIL return b_4c8<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_4c7<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4c7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0xfe}, 0, 0));
            static_assert(!aot::is_known<traits>(0xfe));
            gas -= aot::gas_of<traits>({0xfe}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_4c8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x60, 0x51, 0x83, 0x63, 0x16, 0x7c, 0x02, 0x81, 0x52, 0x60, 0x01, 0x80, 0x83, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x82, 0x81, 0x52, 0x60, 0x01, 0x92, 0x50, 0x50, 0x50, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x60, 0x87, 0x80, 0x3b, 0x15, 0x80, 0x15, 0x61, 0x57}, 6, 6));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x60, 0x51, 0x83, 0x63, 0x16, 0x7c, 0x02, 0x81, 0x52, 0x60, 0x01, 0x80, 0x83, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x82, 0x81, 0x52, 0x60, 0x01, 0x92, 0x50, 0x50, 0x50, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x60, 0x87, 0x80, 0x3b, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = t1 + s2;
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const t4 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s4 = top[-4];
            uint256_t const t5 = uint256_t{0xffffffffull} & s4;
            uint256_t const t6 = aot::shl_c<224>(t5);
            aot::mstore<traits>(ctx, gas, t4, t6);
            uint256_t const t7 = uint256_t{0x4ull} + t4;
            uint256_t const &s3 = top[-3];
            uint256_t const t8 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s3;
            uint256_t const t9 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t8;
            aot::mstore<traits>(ctx, gas, t7, t9);
            uint256_t const t10 = uint256_t{0x20ull} + t7;
            aot::mstore<traits>(ctx, gas, t10, t3);
            uint256_t const t11 = uint256_t{0x20ull} + t10;
            uint256_t const t12 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t13 = t11 - t12;
            uint256_t const &s5 = top[-5];
            ctx->gas_remaining = gas;
            uint256_t r47;
            runtime::extcodesize<traits>(ctx, &r47, &s5);
            gas = ctx->gas_remaining;
            uint256_t const t14 = aot::from_bool(!aot::nonzero(r47));
            uint256_t const t15 = aot::from_bool(!aot::nonzero(t14));
            bool const j52 = aot::nonzero(t15);
            uint256_t const m5 = s5;
            top[-3] = t11;
            top[-2] = uint256_t{0x20ull};
            top[-1] = t12;
            top[0] = t13;
            top[1] = t12;
            top[2] = uint256_t{0x0ull};
            top[3] = m5;
            top[4] = t14;
            top += 4;
            if (j52) { MONAD_AOT_TAIL return b_554<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_550<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_550(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_554(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
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
            if (j8) { MONAD_AOT_TAIL return b_568<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_55f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_55f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x60, 0x80, 0x3e, 0x3d, 0x60, 0xfd}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x60, 0x80, 0x3e, 0x3d, 0x60, 0xfd}) + 0;
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
        [[gnu::noinline]] void b_568(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x60, 0x51, 0x3d, 0x60, 0x81, 0x10, 0x15, 0x61, 0x57}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x60, 0x51, 0x3d, 0x60, 0x81, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(ctx->env.return_data_size)};
            uint256_t const t3 = aot::from_bool(t2 < uint256_t{0x20ull});
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j13 = aot::nonzero(t4);
            top[-3] = t1;
            top[-2] = t2;
            top += -2;
            if (j13) { MONAD_AOT_TAIL return b_57e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_57a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_57a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_57e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x01, 0x90, 0x80, 0x80, 0x51, 0x90, 0x60, 0x01, 0x90, 0x92, 0x91, 0x90, 0x50, 0x50, 0x50, 0x15, 0x15, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x01, 0x90, 0x80, 0x80, 0x51, 0x90, 0x60, 0x01, 0x90, 0x92, 0x91, 0x90, 0x50, 0x50, 0x50, 0x15, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 + s0;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const t3 = uint256_t{0x20ull} + s1;
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            bool const j20 = aot::nonzero(t5);
            top += -2;
            if (j20) { MONAD_AOT_TAIL return b_59a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_596<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_596(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline]] void b_59a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x80, 0x60, 0x01, 0x91, 0x50, 0x50, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x80, 0x60, 0x01, 0x91, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x1ull} + s0;
            top[0] = t1;
            MONAD_AOT_TAIL return b_468<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_5a7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}, 8, 0));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint64_t const jt = aot::jump_offset(s7);
            top += -8;
            if (MONAD_LIKELY(jt < 1780)) {
                MONAD_AOT_TAIL return jump_table<traits>[jt](ctx, bottom, top, gas);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_5b0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x80, 0x60, 0x91, 0x50}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x80, 0x60, 0x91, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0x0ull};
            top += 2;
            MONAD_AOT_TAIL return b_5b8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_5b8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x85, 0x85, 0x90, 0x50, 0x82, 0x10, 0x15, 0x61, 0x57}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x85, 0x85, 0x90, 0x50, 0x82, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::from_bool(s1 < s4);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j9 = aot::nonzero(t2);
            if (j9) { MONAD_AOT_TAIL return b_655<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_5c4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_5c4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x85, 0x85, 0x83, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}, 6, 5));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x85, 0x85, 0x83, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::from_bool(s1 < s4);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j9 = aot::nonzero(t3);
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const m4 = s4;
            uint256_t const m1 = s1;
            top[1] = m5;
            top[2] = m4;
            top[3] = m1;
            top += 3;
            if (j9) { MONAD_AOT_TAIL return b_5d1<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_5d0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_5d0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0xfe}, 0, 0));
            static_assert(!aot::is_known<traits>(0xfe));
            gas -= aot::gas_of<traits>({0xfe}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_5d1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x73, 0x16, 0x73, 0x16, 0x61, 0x85, 0x85, 0x85, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}, 7, 4));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x73, 0x16, 0x73, 0x16, 0x61, 0x85, 0x85, 0x85, 0x81, 0x81, 0x10, 0x15, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = t1 + s2;
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const t4 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t3;
            uint256_t const t5 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t4;
            uint256_t const &s4 = top[-4];
            uint256_t const &s5 = top[-5];
            uint256_t const t6 = aot::from_bool(s4 < s5);
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j21 = aot::nonzero(t8);
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const m5 = s5;
            uint256_t const m4 = s4;
            top[-2] = t5;
            top[-1] = uint256_t{0x8fcull};
            top[0] = m6;
            top[1] = m5;
            top[2] = m4;
            top += 2;
            if (j21) { MONAD_AOT_TAIL return b_615<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_614<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_614(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0xfe}, 0, 0));
            static_assert(!aot::is_known<traits>(0xfe));
            gas -= aot::gas_of<traits>({0xfe}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_615(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x90, 0x81, 0x15, 0x02, 0x90, 0x60, 0x51, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x85, 0x88, 0x88, 0xf1, 0x93, 0x50, 0x50, 0x50, 0x50, 0x15, 0x80, 0x15, 0x61, 0x57}, 5, 6));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x60, 0x02, 0x01, 0x35, 0x90, 0x81, 0x15, 0x02, 0x90, 0x60, 0x51, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x85, 0x88, 0x88, 0xf1, 0x93, 0x50, 0x50, 0x50, 0x50, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::shl_c<5>(s0);
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = t1 + s2;
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const &s3 = top[-3];
            uint256_t const t5 = aot::mul(t4, s3);
            uint256_t const t6 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t7 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t8 = t6 - t7;
            uint256_t const &s4 = top[-4];
            auto const c24 = aot::call<traits>(ctx, gas, t5, s4, t3, t7, t8, t7, uint256_t{0x0ull}, (aot::gas_of<traits>({0x93, 0x50, 0x50, 0x50, 0x50, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(c24));
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            bool const j34 = aot::nonzero(t10);
            top[-4] = t9;
            top += -4;
            if (j34) { MONAD_AOT_TAIL return b_647<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_63e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_63e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x60, 0x80, 0x3e, 0x3d, 0x60, 0xfd}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x60, 0x80, 0x3e, 0x3d, 0x60, 0xfd}) + 0;
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
        [[gnu::noinline]] void b_647(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x81, 0x80, 0x60, 0x01, 0x92, 0x50, 0x50, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x81, 0x80, 0x60, 0x01, 0x92, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0x1ull} + s2;
            top[-2] = t1;
            top += -1;
            MONAD_AOT_TAIL return b_5b8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_655(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x30, 0x73, 0x16, 0x31, 0x90, 0x50, 0x60, 0x81, 0x11, 0x15, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x30, 0x73, 0x16, 0x31, 0x90, 0x50, 0x60, 0x81, 0x11, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            auto const r4 = aot::balance<traits>(ctx, gas, t2);
            gas = ctx->gas_remaining;
            uint256_t const t3 = aot::from_bool(uint256_t{0x0ull} < r4);
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j12 = aot::nonzero(t4);
            top[0] = r4;
            if (j12) { MONAD_AOT_TAIL return b_6c0<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_679<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_679(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x33, 0x73, 0x16, 0x61, 0x82, 0x90, 0x81, 0x15, 0x02, 0x90, 0x60, 0x51, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x85, 0x88, 0x88, 0xf1, 0x93, 0x50, 0x50, 0x50, 0x50, 0x15, 0x80, 0x15, 0x61, 0x57}, 1, 11));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1013)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x33, 0x73, 0x16, 0x61, 0x82, 0x90, 0x81, 0x15, 0x02, 0x90, 0x60, 0x51, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x85, 0x88, 0x88, 0xf1, 0x93, 0x50, 0x50, 0x50, 0x50, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            uint256_t const &s0 = top[0];
            uint256_t const t3 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const t4 = aot::mul(t3, uint256_t{0x8fcull});
            uint256_t const t5 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t6 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t7 = t5 - t6;
            auto const c22 = aot::call<traits>(ctx, gas, t4, t2, s0, t6, t7, t6, uint256_t{0x0ull}, (aot::gas_of<traits>({0x93, 0x50, 0x50, 0x50, 0x50, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(c22));
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            bool const j32 = aot::nonzero(t9);
            top[1] = t8;
            top += 1;
            if (j32) { MONAD_AOT_TAIL return b_6be<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_6b5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6b5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x3d, 0x60, 0x80, 0x3e, 0x3d, 0x60, 0xfd}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x3d, 0x60, 0x80, 0x3e, 0x3d, 0x60, 0xfd}) + 0;
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
        [[gnu::noinline]] void b_6be(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top += -1;
            MONAD_AOT_TAIL return b_6c0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_6c0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint64_t const jt = aot::jump_offset(s6);
            top += -7;
            if (MONAD_LIKELY(jt < 1780)) {
                MONAD_AOT_TAIL return jump_table<traits>[jt](ctx, bottom, top, gas);
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

    template void c_65660051e320731a::run<EvmTraits<MONAD_ETH_OSAKA>>(
        void *, Context *, interpreter::Intercode const *, uint256_t *, void *);
}
