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

// Include portable Keccak to access its static permutation.
// Rename public symbols to avoid collisions with monad_crypto's assembly.
#define SHA3_absorb monad_zkvm_test_sha3_absorb
#define SHA3_squeeze monad_zkvm_test_sha3_squeeze
// NOLINTNEXTLINE(bugprone-suspicious-include)
#include "../../../third_party/openssl/crypto/sha/keccak1600.c"
#undef SHA3_absorb
#undef SHA3_squeeze

// Used only by host tests: computes in software the same Keccak-f[1600]
// permutation as ZisK's precompile.
void monad_keccakf1600(uint64_t state[25])
{
    KeccakF1600((uint64_t(*)[5])state);
}
