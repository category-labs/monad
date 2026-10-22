// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <stdint.h>

// Include ethash's implementation to expose its private permutation for tests:
// the permutation is static, so including the source file is the only way to
// reach it.
// NOLINTNEXTLINE(bugprone-suspicious-include)
#include "../../../third_party/ethash/lib/keccak/keccak.c"

void test_keccak_f(uint64_t (*state)[25])
{
    keccakf1600_generic(*state);
}
