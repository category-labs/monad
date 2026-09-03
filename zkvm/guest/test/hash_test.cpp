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

#include <category/core/bit_primitives.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <unordered_set>
#include <vector>

namespace
{
    constexpr size_t key_count = 256;

    void require(bool const ok, char const *const message)
    {
        if (!ok) {
            std::fprintf(stderr, "Guest hash: %s\n", message);
            std::exit(1);
        }
    }

    void check_initialization(std::array<uint64_t, 4> const &words)
    {
        unsigned char digest[32];
        std::memcpy(digest, words.data(), sizeof(digest));
        monad::bits::set_map_keys(digest);
        for (size_t i = 0; i < words.size(); ++i) {
            uint64_t const expected = words[i] | (i == 3 ? uint64_t{1} : 0);
            require(
                monad::bits::map_keys[i] == expected,
                "seed word not loaded or multiplier not made odd");
        }
    }

    template <size_t Size>
    void check_keys(
        std::array<std::array<unsigned char, Size>, key_count> const &keys,
        uint64_t (*const hash)(unsigned char const *) noexcept)
    {
        for (size_t offset = 0; offset < 8; ++offset) {
            std::unordered_set<uint64_t> hashes;
            for (auto const &key : keys) {
                // End at the allocation boundary so ASan catches overreads.
                std::vector<unsigned char> buffer(Size + offset);
                auto *const p = buffer.data() + offset;
                std::memcpy(p, key.data(), Size);
                uint64_t const h = hash(p);
                require(h == hash(key.data()), "hash depends on alignment");
                require(
                    hashes.insert(h).second,
                    "collision in the cancelling-word regression corpus");
            }
        }
    }

    // Fixed regression corpora, not a general collision-resistance test.
    void check_regressions()
    {
        // Any equal pair of words cancelled in the old 32-byte XOR fold.
        std::array<std::array<unsigned char, 32>, key_count> slots{};
        for (size_t a = 0; a < 4; ++a) {
            for (size_t b = a + 1; b < 4; ++b) {
                for (size_t i = 0; i < slots.size(); ++i) {
                    slots[i].fill(0);
                    uint64_t const word = i * UINT64_C(0x9e3779b97f4a7c15);
                    std::memcpy(slots[i].data() + 8 * a, &word, sizeof(word));
                    std::memcpy(slots[i].data() + 8 * b, &word, sizeof(word));
                }
                check_keys(slots, monad::bits::hash_bytes32);
            }
        }

        // Cancel the address fold's overlapping loads at offsets 0, 8 and 12.
        std::array<std::array<unsigned char, 20>, key_count> addresses{};
        for (size_t i = 0; i < addresses.size(); ++i) {
            auto &key = addresses[i];
            uint64_t const word = i * UINT64_C(0x9e3779b97f4a7c15);
            std::memcpy(key.data() + 8, &word, sizeof(word));
            for (size_t j = 16; j < key.size(); ++j) {
                key[j] = static_cast<unsigned char>(i + j);
            }
            for (size_t j = 0; j < 8; ++j) {
                key[j] = key[j + 8] ^ key[j + 12];
            }
        }
        check_keys(addresses, monad::bits::hash_bytes20);
    }
}

int main()
{
    // Cover zero words and both even and odd multipliers at initialization.
    check_initialization({0, 0, 0, 0});
    constexpr std::array<uint64_t, 4> first{
        0x243F6A8885A308D3ull,
        0x13198A2E03707344ull,
        0xA4093822299F31D0ull,
        0x082EFA98EC4E6C88ull};
    constexpr std::array<uint64_t, 4> second{
        0x1122334455667788ull,
        0x99AABBCCDDEEFF00ull,
        0xFEDCBA9876543210ull,
        0x0123456789ABCDEFull};

    unsigned char const key[32]{};
    check_initialization(first);
    uint64_t const address_hash = monad::bits::hash_bytes20(key);
    uint64_t const slot_hash = monad::bits::hash_bytes32(key);
    check_regressions();

    // Change the seed between runs, with no live guest maps.
    check_initialization(second);
    require(
        monad::bits::hash_bytes20(key) != address_hash,
        "address hash ignored the new seed");
    require(
        monad::bits::hash_bytes32(key) != slot_hash,
        "slot hash ignored the new seed");
    check_regressions();

    // Reusing a seed must reproduce both hashes, independent of prior blocks.
    check_initialization(first);
    require(
        monad::bits::hash_bytes20(key) == address_hash &&
            monad::bits::hash_bytes32(key) == slot_hash,
        "reinitialization did not restore the hashes");

    std::puts("Guest hash: initialization, rekeying and regressions passed");
}
