// Copyright (C) 2026 Category Labs, Inc.
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

// The trie hash is the hash the build selects, on inputs either side of every
// rate boundary of both sponges: keccak256 by default, monad_poseidon2_256 in a
// tree configured with MONAD_ZKVM_L2_TRIE_HASH=poseidon2 -- and then provably
// not keccak256, so a tree where the selection did not reach this translation
// unit fails here rather than as a root mismatch between generator and guest.

#include <category/core/byte_string.hpp>
#include <category/core/keccak.hpp>
#include <category/core/poseidon2.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/core/trie_hash.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstring>

using namespace monad;

TEST(TrieHash, IsTheHashTheBuildSelects)
{
    for (size_t const len : {0, 1, 31, 32, 87, 88, 89, 135, 136, 137, 532}) {
        byte_string in(len, 0);
        for (size_t i = 0; i < len; ++i) {
            in[i] = static_cast<unsigned char>(7 * i + 3);
        }
        auto const got = trie_hash(in);
        auto const keccak = keccak256(in);
        unsigned char poseidon[32];
        monad_poseidon2_256(in.data(), in.size(), poseidon);
#ifdef MONAD_L2_TRIE_HASH_POSEIDON2
        EXPECT_EQ(0, std::memcmp(got.bytes, poseidon, 32)) << "len " << len;
        EXPECT_NE(0, std::memcmp(got.bytes, keccak.bytes, 32)) << "len " << len;
#else
        EXPECT_EQ(0, std::memcmp(got.bytes, keccak.bytes, 32)) << "len " << len;
#endif
    }
}
