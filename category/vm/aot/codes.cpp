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

// Written by aotgen.py from the codes below: not to be edited.

#include <category/vm/aot/aot.hpp>
#include <category/vm/aot/ops.hpp>

namespace monad::vm::aot
{
    using runtime::Context;
    using runtime::StatusCode;

    // 3124 bytes, keccak d0a06b12ac47863b5c7be4185c2deaad1c61557033f56c7d4ea74429cbb25e23
    template <Traits traits>
    void code_d0a06b12ac47863b(
        void *, Context *const ctx, interpreter::Intercode const *,
        uint256_t *const stack_ptr, void *)
    {
        uint256_t const *const bottom = stack_ptr - 1;
        uint256_t *top = stack_ptr - 1;
        int64_t gas = ctx->gas_remaining;
        uint64_t jt;
        static void *const jump_table[] = {
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&B_af,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&B_b7,
            &&bad, &&B_b9, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&B_c4, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&B_cc, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&B_f1, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&B_10c, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&B_139, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&B_147,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&B_152, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&B_187,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&B_1a1, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&B_1ac, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&B_1b4, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&B_1ca, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&B_1d5, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&B_229, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&B_243, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&B_24e, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&B_264, &&bad, &&B_266, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&B_271, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&B_279, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&B_295, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&B_2a0, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&B_2cc, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&B_2e2, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&B_2ed, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&B_2f5, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&B_31a, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&B_335, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&B_362, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&B_370, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&B_37b, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&B_3b0, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&B_3ca, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&B_3d2, &&bad, &&B_3d4, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&B_3df,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&B_42a, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&B_440, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&B_4dd, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&B_548, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&B_556, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&B_573, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&B_57b, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&B_66d, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&B_68c, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&B_6dc, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&B_7b4, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&B_844, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&B_8cf,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&B_9d9, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&B_a27,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&B_ab4, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&B_b05, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&B_b18, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&B_b30, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&B_b9b, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&B_ba9, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&B_bc6, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&B_bce, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&B_bdb, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&B_be3, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad, &&bad,
            &&bad, &&bad, &&bad, &&bad,
        };
        B_0: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x52, 0x60, 0x36, 0x10, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x52, 0x60, 0x36, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, uint256_t{0x60ull});
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x4ull});
            bool const j7 = aot::nonzero(t2);
            if (j7) goto B_af;
        }
        B_d: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x7c, 0x90, 0x04, 0x63, 0x16, 0x80, 0x63, 0x14, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x7c, 0x90, 0x04, 0x63, 0x16, 0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x0ull});
            uint256_t const t2 = aot::shr_c<224>(t1);
            uint256_t const t3 = uint256_t{0xffffffffull} & t2;
            uint256_t const t4 = aot::from_bool(uint256_t{0x6fdde03ull} == t3);
            bool const j11 = aot::nonzero(t4);
            top[1] = t3;
            top += 1;
            if (j11) goto B_b9;
        }
        B_41: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x95ea7b3ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) goto B_147;
        }
        B_4c: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x18160dddull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) goto B_1a1;
        }
        B_57: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x23b872ddull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) goto B_1ca;
        }
        B_62: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x2e1a7d4dull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) goto B_243;
        }
        B_6d: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x313ce567ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) goto B_266;
        }
        B_78: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x70a08231ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) goto B_295;
        }
        B_83: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x95d89b41ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) goto B_2e2;
        }
        B_8e: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xa9059cbbull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) goto B_370;
        }
        B_99: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xd0e30db0ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) goto B_3ca;
        }
        B_a4: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0xdd62ed3eull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) goto B_3d4;
        }
        B_af: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0xb7ull};
            top += 1;
            goto B_440;
        }
        B_b7: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x00}, 0, 0));
            gas -= aot::gas_of<traits>({0x5b, 0x00}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::stop(ctx, gas);
            return;
        }
        B_b9: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j4 = aot::nonzero(t2);
            if (j4) goto B_c4;
        }
        B_c0: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_c4: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0xccull};
            top += 1;
            goto B_4dd;
        }
        B_cc: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x80, 0x80, 0x60, 0x01, 0x82, 0x81, 0x03, 0x82, 0x52, 0x83, 0x81, 0x81, 0x51, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x80, 0x51, 0x90, 0x60, 0x01, 0x90, 0x80, 0x83, 0x83, 0x60}, 1, 9));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x80, 0x80, 0x60, 0x01, 0x82, 0x81, 0x03, 0x82, 0x52, 0x83, 0x81, 0x81, 0x51, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x80, 0x51, 0x90, 0x60, 0x01, 0x90, 0x80, 0x83, 0x83, 0x60}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = uint256_t{0x20ull} + t1;
            uint256_t const t3 = t2 - t1;
            aot::mstore<traits>(ctx, gas, t1, t3);
            uint256_t const &s0 = top[0];
            uint256_t const t4 = aot::mload<traits>(ctx, gas, s0);
            aot::mstore<traits>(ctx, gas, t2, t4);
            uint256_t const t5 = uint256_t{0x20ull} + t2;
            uint256_t const t6 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t7 = uint256_t{0x20ull} + s0;
            top[1] = t1;
            top[2] = t1;
            top[3] = t5;
            top[4] = t7;
            top[5] = t6;
            top[6] = t6;
            top[7] = t5;
            top[8] = t7;
            top[9] = uint256_t{0x0ull};
            top += 9;
        }
        B_f1: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x81, 0x10, 0x15, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x81, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::from_bool(s0 < s3);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j6 = aot::nonzero(t2);
            if (j6) goto B_10c;
        }
        B_fa: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x01, 0x51, 0x81, 0x84, 0x01, 0x52, 0x60, 0x81, 0x01, 0x90, 0x50, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x01, 0x51, 0x81, 0x84, 0x01, 0x52, 0x60, 0x81, 0x01, 0x90, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 + s0;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = s2 + s0;
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = s0 + uint256_t{0x20ull};
            top[0] = t4;
            goto B_f1;
        }
        B_10c: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x90, 0x50, 0x90, 0x81, 0x01, 0x90, 0x60, 0x16, 0x80, 0x15, 0x61, 0x57}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x90, 0x50, 0x90, 0x81, 0x01, 0x90, 0x60, 0x16, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s4 + s6;
            uint256_t const t2 = uint256_t{0x1full} & s4;
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j16 = aot::nonzero(t3);
            top[-6] = t1;
            top[-5] = t2;
            top += -5;
            if (j16) goto B_139;
        }
        B_120: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x03, 0x80, 0x51, 0x60, 0x83, 0x60, 0x03, 0x61, 0x0a, 0x03, 0x19, 0x16, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x03, 0x80, 0x51, 0x60, 0x83, 0x60, 0x03, 0x61, 0x0a, 0x03, 0x19, 0x16, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 - s0;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = uint256_t{0x20ull} - s0;
            auto const e10 = aot::exp<traits>(ctx, gas, uint256_t{0x100ull}, t3);
            gas = ctx->gas_remaining;
            uint256_t const t4 = e10 - uint256_t{0x1ull};
            uint256_t const t5 = ~t4;
            uint256_t const t6 = t5 & t2;
            aot::mstore<traits>(ctx, gas, t1, t6);
            uint256_t const t7 = uint256_t{0x20ull} + t1;
            top[-1] = t7;
        }
        B_139: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x92, 0x50, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x92, 0x50, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s1 - t1;
            aot::finish(ctx, gas, StatusCode::Success, t1, t2);
            return;
        }
        B_147: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j4 = aot::nonzero(t2);
            if (j4) goto B_152;
        }
        B_14e: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_152: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x56}, 0, 6));
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0x24ull});
            top[1] = uint256_t{0x187ull};
            top[2] = t2;
            top[3] = t3;
            top += 3;
            goto B_57b;
        }
        B_187: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x15, 0x15, 0x15, 0x15, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x15, 0x15, 0x15, 0x15, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            aot::mstore<traits>(ctx, gas, t1, t5);
            uint256_t const t6 = uint256_t{0x20ull} + t1;
            uint256_t const t7 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t8 = t6 - t7;
            aot::finish(ctx, gas, StatusCode::Success, t7, t8);
            return;
        }
        B_1a1: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j4 = aot::nonzero(t2);
            if (j4) goto B_1ac;
        }
        B_1a8: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_1ac: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x1b4ull};
            top += 1;
            goto B_66d;
        }
        B_1b4: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const t2 = uint256_t{0x20ull} + t1;
            uint256_t const t3 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t4 = t2 - t3;
            aot::finish(ctx, gas, StatusCode::Success, t3, t4);
            return;
        }
        B_1ca: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j4 = aot::nonzero(t2);
            if (j4) goto B_1d5;
        }
        B_1d1: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_1d5: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x56}, 0, 7));
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t4 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t3;
            uint256_t const t5 = aot::calldataload(ctx, uint256_t{0x44ull});
            top[1] = uint256_t{0x229ull};
            top[2] = t2;
            top[3] = t4;
            top[4] = t5;
            top += 4;
            goto B_68c;
        }
        B_229: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x15, 0x15, 0x15, 0x15, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x15, 0x15, 0x15, 0x15, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            aot::mstore<traits>(ctx, gas, t1, t5);
            uint256_t const t6 = uint256_t{0x20ull} + t1;
            uint256_t const t7 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t8 = t6 - t7;
            aot::finish(ctx, gas, StatusCode::Success, t7, t8);
            return;
        }
        B_243: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j4 = aot::nonzero(t2);
            if (j4) goto B_24e;
        }
        B_24a: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_24e: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x80, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x56}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x80, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            top[1] = uint256_t{0x264ull};
            top[2] = t1;
            top += 2;
            goto B_9d9;
        }
        B_264: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x00}, 0, 0));
            gas -= aot::gas_of<traits>({0x5b, 0x00}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::stop(ctx, gas);
            return;
        }
        B_266: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j4 = aot::nonzero(t2);
            if (j4) goto B_271;
        }
        B_26d: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_271: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x279ull};
            top += 1;
            goto B_b05;
        }
        B_279: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x60, 0x16, 0x60, 0x16, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x60, 0x16, 0x60, 0x16, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0xffull} & s0;
            uint256_t const t3 = uint256_t{0xffull} & t2;
            aot::mstore<traits>(ctx, gas, t1, t3);
            uint256_t const t4 = uint256_t{0x20ull} + t1;
            uint256_t const t5 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t6 = t4 - t5;
            aot::finish(ctx, gas, StatusCode::Success, t5, t6);
            return;
        }
        B_295: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j4 = aot::nonzero(t2);
            if (j4) goto B_2a0;
        }
        B_29c: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_2a0: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x56}, 0, 5));
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            top[1] = uint256_t{0x2ccull};
            top[2] = t2;
            top += 2;
            goto B_b18;
        }
        B_2cc: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const t2 = uint256_t{0x20ull} + t1;
            uint256_t const t3 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t4 = t2 - t3;
            aot::finish(ctx, gas, StatusCode::Success, t3, t4);
            return;
        }
        B_2e2: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j4 = aot::nonzero(t2);
            if (j4) goto B_2ed;
        }
        B_2e9: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_2ed: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x2f5ull};
            top += 1;
            goto B_b30;
        }
        B_2f5: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x80, 0x80, 0x60, 0x01, 0x82, 0x81, 0x03, 0x82, 0x52, 0x83, 0x81, 0x81, 0x51, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x80, 0x51, 0x90, 0x60, 0x01, 0x90, 0x80, 0x83, 0x83, 0x60}, 1, 9));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x80, 0x80, 0x60, 0x01, 0x82, 0x81, 0x03, 0x82, 0x52, 0x83, 0x81, 0x81, 0x51, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x80, 0x51, 0x90, 0x60, 0x01, 0x90, 0x80, 0x83, 0x83, 0x60}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = uint256_t{0x20ull} + t1;
            uint256_t const t3 = t2 - t1;
            aot::mstore<traits>(ctx, gas, t1, t3);
            uint256_t const &s0 = top[0];
            uint256_t const t4 = aot::mload<traits>(ctx, gas, s0);
            aot::mstore<traits>(ctx, gas, t2, t4);
            uint256_t const t5 = uint256_t{0x20ull} + t2;
            uint256_t const t6 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t7 = uint256_t{0x20ull} + s0;
            top[1] = t1;
            top[2] = t1;
            top[3] = t5;
            top[4] = t7;
            top[5] = t6;
            top[6] = t6;
            top[7] = t5;
            top[8] = t7;
            top[9] = uint256_t{0x0ull};
            top += 9;
        }
        B_31a: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x81, 0x10, 0x15, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x81, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::from_bool(s0 < s3);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j6 = aot::nonzero(t2);
            if (j6) goto B_335;
        }
        B_323: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x01, 0x51, 0x81, 0x84, 0x01, 0x52, 0x60, 0x81, 0x01, 0x90, 0x50, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x01, 0x51, 0x81, 0x84, 0x01, 0x52, 0x60, 0x81, 0x01, 0x90, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 + s0;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = s2 + s0;
            aot::mstore<traits>(ctx, gas, t3, t2);
            uint256_t const t4 = s0 + uint256_t{0x20ull};
            top[0] = t4;
            goto B_31a;
        }
        B_335: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x90, 0x50, 0x90, 0x81, 0x01, 0x90, 0x60, 0x16, 0x80, 0x15, 0x61, 0x57}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x90, 0x50, 0x90, 0x81, 0x01, 0x90, 0x60, 0x16, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s4 + s6;
            uint256_t const t2 = uint256_t{0x1full} & s4;
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j16 = aot::nonzero(t3);
            top[-6] = t1;
            top[-5] = t2;
            top += -5;
            if (j16) goto B_362;
        }
        B_349: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x82, 0x03, 0x80, 0x51, 0x60, 0x83, 0x60, 0x03, 0x61, 0x0a, 0x03, 0x19, 0x16, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x82, 0x03, 0x80, 0x51, 0x60, 0x83, 0x60, 0x03, 0x61, 0x0a, 0x03, 0x19, 0x16, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s1 - s0;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = uint256_t{0x20ull} - s0;
            auto const e10 = aot::exp<traits>(ctx, gas, uint256_t{0x100ull}, t3);
            gas = ctx->gas_remaining;
            uint256_t const t4 = e10 - uint256_t{0x1ull};
            uint256_t const t5 = ~t4;
            uint256_t const t6 = t5 & t2;
            aot::mstore<traits>(ctx, gas, t1, t6);
            uint256_t const t7 = uint256_t{0x20ull} + t1;
            top[-1] = t7;
        }
        B_362: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x92, 0x50, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x92, 0x50, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s1 - t1;
            aot::finish(ctx, gas, StatusCode::Success, t1, t2);
            return;
        }
        B_370: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j4 = aot::nonzero(t2);
            if (j4) goto B_37b;
        }
        B_377: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_37b: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x56}, 0, 6));
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0x24ull});
            top[1] = uint256_t{0x3b0ull};
            top[2] = t2;
            top[3] = t3;
            top += 3;
            goto B_bce;
        }
        B_3b0: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x15, 0x15, 0x15, 0x15, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x15, 0x15, 0x15, 0x15, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            aot::mstore<traits>(ctx, gas, t1, t5);
            uint256_t const t6 = uint256_t{0x20ull} + t1;
            uint256_t const t7 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t8 = t6 - t7;
            aot::finish(ctx, gas, StatusCode::Success, t7, t8);
            return;
        }
        B_3ca: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x61, 0x56}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            top[1] = uint256_t{0x3d2ull};
            top += 1;
            goto B_440;
        }
        B_3d2: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x00}, 0, 0));
            gas -= aot::gas_of<traits>({0x5b, 0x00}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::stop(ctx, gas);
            return;
        }
        B_3d4: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j4 = aot::nonzero(t2);
            if (j4) goto B_3df;
        }
        B_3db: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_3df: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x56}, 0, 6));
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x80, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x80, 0x35, 0x73, 0x16, 0x90, 0x60, 0x01, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            uint256_t const t3 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const t4 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t3;
            top[1] = uint256_t{0x42aull};
            top[2] = t2;
            top[3] = t4;
            top += 3;
            goto B_be3;
        }
        B_42a: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}, 1, 4));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t1, s0);
            uint256_t const t2 = uint256_t{0x20ull} + t1;
            uint256_t const t3 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t4 = t2 - t3;
            aot::finish(ctx, gas, StatusCode::Success, t3, t4);
            return;
        }
        B_440: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x60, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x82, 0x82, 0x54, 0x01, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x33, 0x73, 0x16, 0x7f, 0x34, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa2, 0x56}, 1, 7));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x60, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x82, 0x82, 0x54, 0x01, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x33, 0x73, 0x16, 0x7f, 0x34, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa2, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t2 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t3 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t2;
            uint256_t const t4 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t3;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t4);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const t5 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t6 = aot::sload<traits>(ctx, gas, t5);
            uint256_t const t7 = t6 + t1;
            aot::sstore<traits>(ctx, gas, t5, t7, (aot::gas_of<traits>({0x50, 0x33, 0x73, 0x16, 0x7f, 0x34, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa2, 0x56}) + 0));
            uint256_t const t8 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t9 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t8;
            uint256_t const t10 = ::monad::load_be<uint256_t>(ctx->env.value);
            uint256_t const t11 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t11, t10);
            uint256_t const t12 = uint256_t{0x20ull} + t11;
            uint256_t const t13 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t14 = t12 - t13;
            aot::log2<traits>(ctx, gas, t13, t14, uint256_t{0xc2402c5c5cc9109cull, 0x4eb5b0d3c460751ull, 0x59f4d29a8bfc6cdaull, 0xe1fffcc4923d04b5ull}, t9);
            gas = ctx->gas_remaining;
            uint256_t const &s0 = top[0];
            jt = aot::jump_offset(s0);
            top += -1;
            goto dyn;
        }
        B_4dd: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x80, 0x54, 0x60, 0x81, 0x60, 0x16, 0x15, 0x61, 0x02, 0x03, 0x16, 0x60, 0x90, 0x04, 0x80, 0x60, 0x01, 0x60, 0x80, 0x91, 0x04, 0x02, 0x60, 0x01, 0x60, 0x51, 0x90, 0x81, 0x01, 0x60, 0x52, 0x80, 0x92, 0x91, 0x90, 0x81, 0x81, 0x52, 0x60, 0x01, 0x82, 0x80, 0x54, 0x60, 0x81, 0x60, 0x16, 0x15, 0x61, 0x02, 0x03, 0x16, 0x60, 0x90, 0x04, 0x80, 0x15, 0x61, 0x57}, 0, 9));
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x80, 0x54, 0x60, 0x81, 0x60, 0x16, 0x15, 0x61, 0x02, 0x03, 0x16, 0x60, 0x90, 0x04, 0x80, 0x60, 0x01, 0x60, 0x80, 0x91, 0x04, 0x02, 0x60, 0x01, 0x60, 0x51, 0x90, 0x81, 0x01, 0x60, 0x52, 0x80, 0x92, 0x91, 0x90, 0x81, 0x81, 0x52, 0x60, 0x01, 0x82, 0x80, 0x54, 0x60, 0x81, 0x60, 0x16, 0x15, 0x61, 0x02, 0x03, 0x16, 0x60, 0x90, 0x04, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::sload<traits>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t2 = uint256_t{0x1ull} & t1;
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t4 = aot::shl_c<8>(t3);
            uint256_t const t5 = t4 - uint256_t{0x1ull};
            uint256_t const t6 = t5 & t1;
            uint256_t const t7 = aot::shr_c<1>(t6);
            uint256_t const t8 = uint256_t{0x1full} + t7;
            uint256_t const t9 = aot::shr_c<5>(t8);
            uint256_t const t10 = aot::shl_c<5>(t9);
            uint256_t const t11 = uint256_t{0x20ull} + t10;
            uint256_t const t12 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t13 = t12 + t11;
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t13);
            aot::mstore<traits>(ctx, gas, t12, t7);
            uint256_t const t14 = uint256_t{0x20ull} + t12;
            uint256_t const t15 = aot::sload<traits>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t16 = uint256_t{0x1ull} & t15;
            uint256_t const t17 = aot::from_bool(!aot::nonzero(t16));
            uint256_t const t18 = aot::shl_c<8>(t17);
            uint256_t const t19 = t18 - uint256_t{0x1ull};
            uint256_t const t20 = t19 & t15;
            uint256_t const t21 = aot::shr_c<1>(t20);
            uint256_t const t22 = aot::from_bool(!aot::nonzero(t21));
            bool const j60 = aot::nonzero(t22);
            top[1] = t12;
            top[2] = uint256_t{0x0ull};
            top[3] = t7;
            top[4] = t14;
            top[5] = uint256_t{0x0ull};
            top[6] = t21;
            top += 6;
            if (j60) goto B_573;
        }
        B_52d: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x60, 0x10, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x60, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x1full} < s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) goto B_548;
        }
        B_535: {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x80, 0x83, 0x54, 0x04, 0x02, 0x83, 0x52, 0x91, 0x60, 0x01, 0x91, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x80, 0x83, 0x54, 0x04, 0x02, 0x83, 0x52, 0x91, 0x60, 0x01, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::sload<traits>(ctx, gas, s1);
            uint256_t const t2 = aot::shr_c<8>(t1);
            uint256_t const t3 = aot::shl_c<8>(t2);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, t3);
            uint256_t const t4 = uint256_t{0x20ull} + s2;
            top[-2] = t4;
            goto B_573;
        }
        B_548: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x01, 0x91, 0x90, 0x60, 0x52, 0x60, 0x60, 0x20, 0x90}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x01, 0x91, 0x90, 0x60, 0x52, 0x60, 0x60, 0x20, 0x90}) + 6;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s2 + s0;
            uint256_t const &s1 = top[-1];
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, s1);
            uint256_t const t2 = aot::sha3_n<traits, 32>(ctx, gas, uint256_t{0x0ull});
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[-1] = t2;
            top[0] = m2;
        }
        B_556: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x54, 0x81, 0x52, 0x90, 0x60, 0x01, 0x90, 0x60, 0x01, 0x80, 0x83, 0x11, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x54, 0x81, 0x52, 0x90, 0x60, 0x01, 0x90, 0x60, 0x01, 0x80, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::sload<traits>(ctx, gas, s1);
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, t1);
            uint256_t const t2 = uint256_t{0x1ull} + s1;
            uint256_t const t3 = uint256_t{0x20ull} + s0;
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = aot::from_bool(t3 < s2);
            bool const j15 = aot::nonzero(t4);
            top[-1] = t2;
            top[0] = t3;
            if (j15) goto B_556;
        }
        B_56a: {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x90, 0x03, 0x60, 0x16, 0x82, 0x01, 0x91}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x90, 0x03, 0x60, 0x16, 0x82, 0x01, 0x91}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s0 - s2;
            uint256_t const t2 = uint256_t{0x1full} & t1;
            uint256_t const t3 = s2 + t2;
            uint256_t const m2 = s2;
            top[-2] = t3;
            top[0] = m2;
        }
        B_573: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x81, 0x56}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x81, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            jt = aot::jump_offset(s6);
            top += -5;
            goto dyn;
        }
        B_57b: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x60, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x85, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x81, 0x90, 0x55, 0x50, 0x82, 0x73, 0x16, 0x33, 0x73, 0x16, 0x7f, 0x84, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa3, 0x60, 0x90, 0x50, 0x92, 0x91, 0x50, 0x50, 0x56}, 3, 9));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x60, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x85, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x81, 0x90, 0x55, 0x50, 0x82, 0x73, 0x16, 0x33, 0x73, 0x16, 0x7f, 0x84, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa3, 0x60, 0x90, 0x50, 0x92, 0x91, 0x50, 0x50, 0x56}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            uint256_t const t3 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t2;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x4ull});
            uint256_t const t4 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const &s1 = top[-1];
            uint256_t const t5 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s1;
            uint256_t const t6 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t5;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t6);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t4);
            uint256_t const t7 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const &s0 = top[0];
            aot::sstore<traits>(ctx, gas, t7, s0, (aot::gas_of<traits>({0x50, 0x82, 0x73, 0x16, 0x33, 0x73, 0x16, 0x7f, 0x84, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa3, 0x60, 0x90, 0x50, 0x92, 0x91, 0x50, 0x50, 0x56}) + 0));
            uint256_t const t8 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s1;
            uint256_t const t9 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t10 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t9;
            uint256_t const t11 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t11, s0);
            uint256_t const t12 = uint256_t{0x20ull} + t11;
            uint256_t const t13 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t14 = t12 - t13;
            aot::log3<traits>(ctx, gas, t13, t14, uint256_t{0x5b200ac8c7c3b925ull, 0xdd0314c0f7b2291eull, 0xd14f71427d1e84f3ull, 0x8c5be1e5ebec7d5bull}, t10, t8);
            gas = ctx->gas_remaining;
            uint256_t const &s2 = top[-2];
            jt = aot::jump_offset(s2);
            top[-2] = uint256_t{0x1ull};
            top += -2;
            goto dyn;
        }
        B_66d: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x30, 0x73, 0x16, 0x31, 0x90, 0x50, 0x90, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x30, 0x73, 0x16, 0x31, 0x90, 0x50, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.recipient);
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            auto const r5 = aot::balance<traits>(ctx, gas, t2);
            gas = ctx->gas_remaining;
            uint256_t const &s0 = top[0];
            jt = aot::jump_offset(s0);
            top[0] = r5;
            goto dyn;
        }
        B_68c: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x81, 0x60, 0x60, 0x86, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x54, 0x10, 0x15, 0x15, 0x15, 0x61, 0x57}, 3, 6));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x81, 0x60, 0x60, 0x86, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x54, 0x10, 0x15, 0x15, 0x15, 0x61, 0x57}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s2;
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const t3 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t4 = aot::sload<traits>(ctx, gas, t3);
            uint256_t const &s0 = top[0];
            uint256_t const t5 = aot::from_bool(t4 < s0);
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            bool const j27 = aot::nonzero(t8);
            top[1] = uint256_t{0x0ull};
            top += 1;
            if (j27) goto B_6dc;
        }
        B_6d8: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_6dc: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x33, 0x73, 0x16, 0x84, 0x73, 0x16, 0x14, 0x15, 0x80, 0x15, 0x61, 0x57}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x33, 0x73, 0x16, 0x84, 0x73, 0x16, 0x14, 0x15, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s3;
            uint256_t const t4 = aot::from_bool(t3 == t2);
            uint256_t const t5 = aot::from_bool(!aot::nonzero(t4));
            uint256_t const t6 = aot::from_bool(!aot::nonzero(t5));
            bool const j12 = aot::nonzero(t6);
            top[1] = t5;
            top += 1;
            if (j12) goto B_7b4;
        }
        B_713: {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x7f, 0x60, 0x60, 0x86, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x54, 0x14, 0x15}, 5, 4));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x7f, 0x60, 0x60, 0x86, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x54, 0x14, 0x15}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s4;
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x4ull});
            uint256_t const t3 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t4 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t5 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t4;
            uint256_t const t6 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t5;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t6);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t3);
            uint256_t const t7 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t8 = aot::sload<traits>(ctx, gas, t7);
            uint256_t const t9 = aot::from_bool(t8 == uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull});
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            top[0] = t10;
        }
        B_7b4: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x15, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(!aot::nonzero(s0));
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) goto B_8cf;
        }
        B_7ba: {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x60, 0x60, 0x86, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x54, 0x10, 0x15, 0x15, 0x15, 0x61, 0x57}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x60, 0x60, 0x86, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x54, 0x10, 0x15, 0x15, 0x15, 0x61, 0x57}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s3;
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x4ull});
            uint256_t const t3 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t4 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t5 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t4;
            uint256_t const t6 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t5;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t6);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t3);
            uint256_t const t7 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t8 = aot::sload<traits>(ctx, gas, t7);
            uint256_t const &s1 = top[-1];
            uint256_t const t9 = aot::from_bool(t8 < s1);
            uint256_t const t10 = aot::from_bool(!aot::nonzero(t9));
            uint256_t const t11 = aot::from_bool(!aot::nonzero(t10));
            uint256_t const t12 = aot::from_bool(!aot::nonzero(t11));
            bool const j42 = aot::nonzero(t12);
            if (j42) goto B_844;
        }
        B_840: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_844: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x60, 0x60, 0x86, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x82, 0x82, 0x54, 0x03, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x60, 0x60, 0x86, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x82, 0x82, 0x54, 0x03, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s3;
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x4ull});
            uint256_t const t3 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t4 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t5 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t4;
            uint256_t const t6 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t5;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t6);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t3);
            uint256_t const t7 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t8 = aot::sload<traits>(ctx, gas, t7);
            uint256_t const &s1 = top[-1];
            uint256_t const t9 = t8 - s1;
            aot::sstore<traits>(ctx, gas, t7, t9, (aot::gas_of<traits>({0x50}) + 0));
        }
        B_8cf: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x60, 0x60, 0x86, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x82, 0x82, 0x54, 0x03, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x81, 0x60, 0x60, 0x85, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x82, 0x82, 0x54, 0x01, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x82, 0x73, 0x16, 0x84, 0x73, 0x16, 0x7f, 0x84, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa3, 0x60, 0x90, 0x50, 0x93, 0x92, 0x50, 0x50, 0x50, 0x56}, 5, 8));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x60, 0x60, 0x86, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x82, 0x82, 0x54, 0x03, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x81, 0x60, 0x60, 0x85, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x82, 0x82, 0x54, 0x01, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x82, 0x73, 0x16, 0x84, 0x73, 0x16, 0x7f, 0x84, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa3, 0x60, 0x90, 0x50, 0x93, 0x92, 0x50, 0x50, 0x50, 0x56}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s3;
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const t3 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t4 = aot::sload<traits>(ctx, gas, t3);
            uint256_t const &s1 = top[-1];
            uint256_t const t5 = t4 - s1;
            aot::sstore<traits>(ctx, gas, t3, t5, (aot::gas_of<traits>({0x50, 0x81, 0x60, 0x60, 0x85, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x82, 0x82, 0x54, 0x01, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x82, 0x73, 0x16, 0x84, 0x73, 0x16, 0x7f, 0x84, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa3, 0x60, 0x90, 0x50, 0x93, 0x92, 0x50, 0x50, 0x50, 0x56}) + 12));
            uint256_t const &s2 = top[-2];
            uint256_t const t6 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s2;
            uint256_t const t7 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t6;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t7);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const t8 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t9 = aot::sload<traits>(ctx, gas, t8);
            uint256_t const t10 = t9 + s1;
            aot::sstore<traits>(ctx, gas, t8, t10, (aot::gas_of<traits>({0x50, 0x82, 0x73, 0x16, 0x84, 0x73, 0x16, 0x7f, 0x84, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa3, 0x60, 0x90, 0x50, 0x93, 0x92, 0x50, 0x50, 0x50, 0x56}) + 0));
            uint256_t const t11 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s2;
            uint256_t const t12 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & s3;
            uint256_t const t13 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            aot::mstore<traits>(ctx, gas, t13, s1);
            uint256_t const t14 = uint256_t{0x20ull} + t13;
            uint256_t const t15 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t16 = t14 - t15;
            aot::log3<traits>(ctx, gas, t15, t16, uint256_t{0x28f55a4df523b3efull, 0x952ba7f163c4a116ull, 0x69c2b068fc378daaull, 0xddf252ad1be2c89bull}, t12, t11);
            gas = ctx->gas_remaining;
            uint256_t const &s4 = top[-4];
            jt = aot::jump_offset(s4);
            top[-4] = uint256_t{0x1ull};
            top += -4;
            goto dyn;
        }
        B_9d9: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x60, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x54, 0x10, 0x15, 0x15, 0x15, 0x61, 0x57}, 1, 5));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x60, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x54, 0x10, 0x15, 0x15, 0x15, 0x61, 0x57}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            uint256_t const t3 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t2;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const t4 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t5 = aot::sload<traits>(ctx, gas, t4);
            uint256_t const &s0 = top[0];
            uint256_t const t6 = aot::from_bool(t5 < s0);
            uint256_t const t7 = aot::from_bool(!aot::nonzero(t6));
            uint256_t const t8 = aot::from_bool(!aot::nonzero(t7));
            uint256_t const t9 = aot::from_bool(!aot::nonzero(t8));
            bool const j26 = aot::nonzero(t9);
            if (j26) goto B_a27;
        }
        B_a23: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_a27: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x80, 0x60, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x82, 0x82, 0x54, 0x03, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x33, 0x73, 0x16, 0x61, 0x82, 0x90, 0x81, 0x15, 0x02, 0x90, 0x60, 0x51, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x85, 0x88, 0x88, 0xf1, 0x93, 0x50, 0x50, 0x50, 0x50, 0x15, 0x15, 0x61, 0x57}, 1, 11));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1013)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x80, 0x60, 0x60, 0x33, 0x73, 0x16, 0x73, 0x16, 0x81, 0x52, 0x60, 0x01, 0x90, 0x81, 0x52, 0x60, 0x01, 0x60, 0x20, 0x60, 0x82, 0x82, 0x54, 0x03, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x33, 0x73, 0x16, 0x61, 0x82, 0x90, 0x81, 0x15, 0x02, 0x90, 0x60, 0x51, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x85, 0x88, 0x88, 0xf1, 0x93, 0x50, 0x50, 0x50, 0x50, 0x15, 0x15, 0x61, 0x57}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            uint256_t const t3 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t2;
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t3);
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const t4 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t5 = aot::sload<traits>(ctx, gas, t4);
            uint256_t const &s0 = top[0];
            uint256_t const t6 = t5 - s0;
            aot::sstore<traits>(ctx, gas, t4, t6, (aot::gas_of<traits>({0x50, 0x33, 0x73, 0x16, 0x61, 0x82, 0x90, 0x81, 0x15, 0x02, 0x90, 0x60, 0x51, 0x60, 0x60, 0x51, 0x80, 0x83, 0x03, 0x81, 0x85, 0x88, 0x88, 0xf1, 0x93, 0x50, 0x50, 0x50, 0x50, 0x15, 0x15, 0x61, 0x57}) + 0));
            uint256_t const t7 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t8 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t7;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const t10 = aot::mul(t9, uint256_t{0x8fcull});
            uint256_t const t11 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t12 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t13 = t11 - t12;
            auto const c54 = aot::call<traits>(ctx, gas, t10, t8, s0, t12, t13, t12, uint256_t{0x0ull}, (aot::gas_of<traits>({0x93, 0x50, 0x50, 0x50, 0x50, 0x15, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t14 = aot::from_bool(!aot::nonzero(c54));
            uint256_t const t15 = aot::from_bool(!aot::nonzero(t14));
            bool const j63 = aot::nonzero(t15);
            if (j63) goto B_ab4;
        }
        B_ab0: {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }
        B_ab4: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x33, 0x73, 0x16, 0x7f, 0x82, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa2, 0x50, 0x56}, 2, 7));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x33, 0x73, 0x16, 0x7f, 0x82, 0x60, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x01, 0x91, 0x50, 0x50, 0x60, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa2, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const t2 = uint256_t{0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffull, 0x0ull} & t1;
            uint256_t const t3 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t3, s0);
            uint256_t const t4 = uint256_t{0x20ull} + t3;
            uint256_t const t5 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t6 = t4 - t5;
            aot::log2<traits>(ctx, gas, t5, t6, uint256_t{0x7268a95bf5081b65ull, 0x30d808c7d98cb3bfull, 0xbd6d0e038bea71dull, 0x7fcf532c15f0a6dbull}, t2);
            gas = ctx->gas_remaining;
            uint256_t const &s1 = top[-1];
            jt = aot::jump_offset(s1);
            top += -2;
            goto dyn;
        }
        B_b05: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x90, 0x54, 0x90, 0x61, 0x0a, 0x90, 0x04, 0x60, 0x16, 0x81, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x90, 0x54, 0x90, 0x61, 0x0a, 0x90, 0x04, 0x60, 0x16, 0x81, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::sload<traits>(ctx, gas, uint256_t{0x2ull});
            uint256_t const t2 = uint256_t{0xffull} & t1;
            uint256_t const &s0 = top[0];
            jt = aot::jump_offset(s0);
            top[1] = t2;
            top += 1;
            goto dyn;
        }
        B_b18: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x52, 0x80, 0x60, 0x52, 0x60, 0x60, 0x20, 0x60, 0x91, 0x50, 0x90, 0x50, 0x54, 0x81, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x52, 0x80, 0x60, 0x52, 0x60, 0x60, 0x20, 0x60, 0x91, 0x50, 0x90, 0x50, 0x54, 0x81, 0x56}) + 12;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x3ull});
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, s0);
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t2 = aot::sload<traits>(ctx, gas, t1);
            uint256_t const &s1 = top[-1];
            jt = aot::jump_offset(s1);
            top[0] = t2;
            goto dyn;
        }
        B_b30: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x80, 0x54, 0x60, 0x81, 0x60, 0x16, 0x15, 0x61, 0x02, 0x03, 0x16, 0x60, 0x90, 0x04, 0x80, 0x60, 0x01, 0x60, 0x80, 0x91, 0x04, 0x02, 0x60, 0x01, 0x60, 0x51, 0x90, 0x81, 0x01, 0x60, 0x52, 0x80, 0x92, 0x91, 0x90, 0x81, 0x81, 0x52, 0x60, 0x01, 0x82, 0x80, 0x54, 0x60, 0x81, 0x60, 0x16, 0x15, 0x61, 0x02, 0x03, 0x16, 0x60, 0x90, 0x04, 0x80, 0x15, 0x61, 0x57}, 0, 9));
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x80, 0x54, 0x60, 0x81, 0x60, 0x16, 0x15, 0x61, 0x02, 0x03, 0x16, 0x60, 0x90, 0x04, 0x80, 0x60, 0x01, 0x60, 0x80, 0x91, 0x04, 0x02, 0x60, 0x01, 0x60, 0x51, 0x90, 0x81, 0x01, 0x60, 0x52, 0x80, 0x92, 0x91, 0x90, 0x81, 0x81, 0x52, 0x60, 0x01, 0x82, 0x80, 0x54, 0x60, 0x81, 0x60, 0x16, 0x15, 0x61, 0x02, 0x03, 0x16, 0x60, 0x90, 0x04, 0x80, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::sload<traits>(ctx, gas, uint256_t{0x1ull});
            uint256_t const t2 = uint256_t{0x1ull} & t1;
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            uint256_t const t4 = aot::shl_c<8>(t3);
            uint256_t const t5 = t4 - uint256_t{0x1ull};
            uint256_t const t6 = t5 & t1;
            uint256_t const t7 = aot::shr_c<1>(t6);
            uint256_t const t8 = uint256_t{0x1full} + t7;
            uint256_t const t9 = aot::shr_c<5>(t8);
            uint256_t const t10 = aot::shl_c<5>(t9);
            uint256_t const t11 = uint256_t{0x20ull} + t10;
            uint256_t const t12 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t13 = t12 + t11;
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, t13);
            aot::mstore<traits>(ctx, gas, t12, t7);
            uint256_t const t14 = uint256_t{0x20ull} + t12;
            uint256_t const t15 = aot::sload<traits>(ctx, gas, uint256_t{0x1ull});
            uint256_t const t16 = uint256_t{0x1ull} & t15;
            uint256_t const t17 = aot::from_bool(!aot::nonzero(t16));
            uint256_t const t18 = aot::shl_c<8>(t17);
            uint256_t const t19 = t18 - uint256_t{0x1ull};
            uint256_t const t20 = t19 & t15;
            uint256_t const t21 = aot::shr_c<1>(t20);
            uint256_t const t22 = aot::from_bool(!aot::nonzero(t21));
            bool const j60 = aot::nonzero(t22);
            top[1] = t12;
            top[2] = uint256_t{0x1ull};
            top[3] = t7;
            top[4] = t14;
            top[5] = uint256_t{0x1ull};
            top[6] = t21;
            top += 6;
            if (j60) goto B_bc6;
        }
        B_b80: {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x60, 0x10, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x60, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x1full} < s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) goto B_b9b;
        }
        B_b88: {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x80, 0x83, 0x54, 0x04, 0x02, 0x83, 0x52, 0x91, 0x60, 0x01, 0x91, 0x61, 0x56}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x80, 0x83, 0x54, 0x04, 0x02, 0x83, 0x52, 0x91, 0x60, 0x01, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::sload<traits>(ctx, gas, s1);
            uint256_t const t2 = aot::shr_c<8>(t1);
            uint256_t const t3 = aot::shl_c<8>(t2);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, t3);
            uint256_t const t4 = uint256_t{0x20ull} + s2;
            top[-2] = t4;
            goto B_bc6;
        }
        B_b9b: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x01, 0x91, 0x90, 0x60, 0x52, 0x60, 0x60, 0x20, 0x90}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x01, 0x91, 0x90, 0x60, 0x52, 0x60, 0x60, 0x20, 0x90}) + 6;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s2 + s0;
            uint256_t const &s1 = top[-1];
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, s1);
            uint256_t const t2 = aot::sha3_n<traits, 32>(ctx, gas, uint256_t{0x0ull});
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[-1] = t2;
            top[0] = m2;
        }
        B_ba9: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x54, 0x81, 0x52, 0x90, 0x60, 0x01, 0x90, 0x60, 0x01, 0x80, 0x83, 0x11, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x54, 0x81, 0x52, 0x90, 0x60, 0x01, 0x90, 0x60, 0x01, 0x80, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::sload<traits>(ctx, gas, s1);
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, s0, t1);
            uint256_t const t2 = uint256_t{0x1ull} + s1;
            uint256_t const t3 = uint256_t{0x20ull} + s0;
            uint256_t const &s2 = top[-2];
            uint256_t const t4 = aot::from_bool(t3 < s2);
            bool const j15 = aot::nonzero(t4);
            top[-1] = t2;
            top[0] = t3;
            if (j15) goto B_ba9;
        }
        B_bbd: {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x90, 0x03, 0x60, 0x16, 0x82, 0x01, 0x91}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x90, 0x03, 0x60, 0x16, 0x82, 0x01, 0x91}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s0 - s2;
            uint256_t const t2 = uint256_t{0x1full} & t1;
            uint256_t const t3 = s2 + t2;
            uint256_t const m2 = s2;
            top[-2] = t3;
            top[0] = m2;
        }
        B_bc6: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x81, 0x56}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x81, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            jt = aot::jump_offset(s6);
            top += -5;
            goto dyn;
        }
        B_bce: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x61, 0x33, 0x84, 0x84, 0x61, 0x56}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x61, 0x33, 0x84, 0x84, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = runtime::uint256_from_address(ctx->env.sender);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x0ull};
            top[2] = uint256_t{0xbdbull};
            top[3] = t1;
            top[4] = m1;
            top[5] = m0;
            top += 5;
            goto B_68c;
        }
        B_bdb: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x50, 0x92, 0x91, 0x50, 0x50, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x50, 0x92, 0x91, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            jt = aot::jump_offset(s4);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-4] = m0;
            top += -4;
            goto dyn;
        }
        B_be3: {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x60, 0x52, 0x81, 0x60, 0x52, 0x60, 0x60, 0x20, 0x60, 0x52, 0x80, 0x60, 0x52, 0x60, 0x60, 0x20, 0x60, 0x91, 0x50, 0x91, 0x50, 0x50, 0x54, 0x81, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x60, 0x52, 0x81, 0x60, 0x52, 0x60, 0x60, 0x20, 0x60, 0x52, 0x80, 0x60, 0x52, 0x60, 0x60, 0x20, 0x60, 0x91, 0x50, 0x91, 0x50, 0x50, 0x54, 0x81, 0x56}) + 24;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, uint256_t{0x4ull});
            uint256_t const &s1 = top[-1];
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, s1);
            uint256_t const t1 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            aot::mstore_c<traits, 32u, 64u, 6>(ctx, gas, t1);
            uint256_t const &s0 = top[0];
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, s0);
            uint256_t const t2 = aot::sha3_n<traits, 64>(ctx, gas, uint256_t{0x0ull});
            uint256_t const t3 = aot::sload<traits>(ctx, gas, t2);
            uint256_t const &s2 = top[-2];
            jt = aot::jump_offset(s2);
            top[-1] = t3;
            top += -1;
            goto dyn;
        }
    B_end:
        aot::stop(ctx, gas);
        return;
    dyn:
        if (MONAD_LIKELY(jt < 3124)) {
            goto *jump_table[jt];
        }
    bad:
        ctx->exit(StatusCode::Error);
    }

    using Osaka = EvmTraits<MONAD_ETH_OSAKA>;

    constexpr Entry entry_0{
        {0x3b8647ac126ba0d0u, 0xadea2d5c18e47b5cu, 0x7d6cf5337055611cu, 0x235eb2cb2944a74eu},
        3124,
        &code_d0a06b12ac47863b<Osaka>,
        nullptr};

    Entry const *const table[256] = {
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        &entry_0, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
    };
}
