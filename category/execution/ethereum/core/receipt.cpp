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

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/receipt.hpp>

#include <cstdint>
#ifdef MONAD_ZKVM_ZISK
    #include <category/core/likely.h>

    #include <cstddef>
#endif

MONAD_NAMESPACE_BEGIN

void set_3_bits(Receipt::Bloom &bloom, byte_string_view const bytes)
{
    // YP Eqn 29
    auto const hash = keccak256(bytes);
    // The three 16-bit big-endian chunks are the hash's first six bytes, so
    // one 64-bit big-endian load holds them all, chunk i at bit 48 - 16i.
    uint64_t const chunks = load_be_unsafe<uint64_t>(hash.bytes);
    for (unsigned i = 0; i < 3; ++i) {
        uint64_t const bit = (chunks >> (48 - 16 * i)) & 2047u;
        bloom[255u - bit / 8u] |= static_cast<unsigned char>(1u << (bit & 7u));
    }
}

#ifdef MONAD_ZKVM_ZISK
namespace
{
    // A block's logs repeat their contracts and event signatures, and the
    // Keccak-f memo spares a repeat its permutation but not the sponge around
    // it. A hash's first word is kept by its input, in a direct-mapped table;
    // bit 63, which no chunk reads, marks a filled entry. An entry takes 64
    // bytes so that its index is a shift.
    struct BloomMemo
    {
        uint64_t key[4];
        uint64_t chunks;
        uint64_t pad[3];
    };

    constinit BloomMemo topic_memo[512]{};
    constinit BloomMemo address_memo[256]{};

    using word_alias = uint64_t __attribute__((may_alias));

    uint64_t bloom_chunks(byte_string_view const bytes)
    {
        auto const hash = keccak256(bytes);
        return load_be_unsafe<uint64_t>(hash.bytes) | (uint64_t{1} << 63);
    }

    // set_3_bits on the bloom's words: byte 255 - bit / 8 is byte
    // (bit / 8) ^ 7 of word (bit / 64) ^ 31, and bit bit % 8 of that byte is
    // the word's bit (bit ^ 56) % 64.
    [[gnu::always_inline]] inline void
    set_3_bits_in(word_alias *const words, uint64_t const chunks)
    {
        for (unsigned i = 0; i < 3; ++i) {
            uint64_t const bit = (chunks >> (48 - 16 * i)) & 2047u;
            words[(bit >> 6) ^ 31u] |= uint64_t{1} << ((bit ^ 56u) & 63u);
        }
    }
}

void populate_bloom(Receipt::Bloom &bloom, Receipt::Log const &log)
{
    // YP Eqn 28
    static_assert(offsetof(Receipt, bloom) % 8 == 0);
    static_assert(offsetof(Receipt::Log, address) % 8 == 0);
    auto *const words = reinterpret_cast<word_alias *>(bloom.data());
    {
        auto const *const a =
            reinterpret_cast<word_alias const *>(log.address.bytes);
        uint64_t const a2 =
            *reinterpret_cast<uint32_t const *>(log.address.bytes + 16);
        BloomMemo &e = address_memo[(a[1] ^ a2) & 255u];
        uint64_t chunks = e.chunks;
        if (MONAD_UNLIKELY(
                e.key[0] != a[0] || e.key[1] != a[1] || e.key[2] != a2 ||
                chunks == 0)) {
            e.key[0] = a[0];
            e.key[1] = a[1];
            e.key[2] = a2;
            chunks = bloom_chunks(to_byte_string_view(log.address.bytes));
            e.chunks = chunks;
        }
        set_3_bits_in(words, chunks);
    }
    for (auto const &topic : log.topics) {
        auto const *const t = reinterpret_cast<word_alias const *>(topic.bytes);
        uint64_t const t3 = t[3];
        BloomMemo &e = topic_memo[(t3 ^ __builtin_bswap64(t3)) & 511u];
        uint64_t chunks = e.chunks;
        if (MONAD_UNLIKELY(
                e.key[3] != t3 || e.key[0] != t[0] || e.key[1] != t[1] ||
                e.key[2] != t[2] || chunks == 0)) {
            e.key[0] = t[0];
            e.key[1] = t[1];
            e.key[2] = t[2];
            e.key[3] = t3;
            chunks = bloom_chunks(to_byte_string_view(topic.bytes));
            e.chunks = chunks;
        }
        set_3_bits_in(words, chunks);
    }
}
#else
void populate_bloom(Receipt::Bloom &bloom, Receipt::Log const &log)
{
    // YP Eqn 28
    set_3_bits(bloom, to_byte_string_view(log.address.bytes));
    for (auto const &i : log.topics) {
        set_3_bits(bloom, to_byte_string_view(i.bytes));
    }
}
#endif

void Receipt::add_log(Receipt::Log const &log)
{
    logs.push_back(log);
    populate_bloom(bloom, log);
}

MONAD_NAMESPACE_END
