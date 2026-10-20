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

extern "C"
{
#include <blake3.h>
#include <blake3_impl.h>
}

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/lbt/commit.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <span>

MONAD_MPT_NAMESPACE_BEGIN

namespace lbt
{
    namespace
    {
        // Chaining values are copied out as native words; BLAKE3 defines
        // their bytes as little-endian.
        static_assert(std::endian::native == std::endian::little);

        constexpr uint8_t BLOCK_FLAGS = CHUNK_START | CHUNK_END;

        using iv_t = std::array<uint32_t, 8>;
        using block_t = std::array<uint8_t, BLAKE3_BLOCK_LEN>;

        // A single DERIVE_KEY_MATERIAL compression; BLAKE3's public
        // derive_key mode gives different bytes.
        iv_t derive_iv(char const (&domain)[33])
        {
            block_t block{};
            std::memcpy(block.data(), domain, 32);
            iv_t iv;
            std::memcpy(iv.data(), IV, sizeof(iv));
            blake3_compress_in_place(
                iv.data(),
                block.data(),
                BLAKE3_BLOCK_LEN,
                0,
                DERIVE_KEY_MATERIAL);
            return iv;
        }

        uint32_t const *leaf_iv()
        {
            static iv_t const iv =
                derive_iv("monad_lbt_leaf_domain___________");
            return iv.data();
        }

        uint8_t const *value_key()
        {
            static iv_t const key =
                derive_iv("monad_lbt_value_domain__________");
            return reinterpret_cast<uint8_t const *>(key.data());
        }

        bytes32_t compress_block(
            uint32_t const *const iv, block_t const &block,
            uint64_t const counter)
        {
            uint32_t cv[8];
            std::memcpy(cv, iv, sizeof(cv));
            blake3_compress_in_place(
                cv, block.data(), BLAKE3_BLOCK_LEN, counter, BLOCK_FLAGS);
            bytes32_t out;
            std::memcpy(out.bytes, cv, sizeof(out.bytes));
            return out;
        }

        void pack_pair(block_t &block, bytes32_t const &l, bytes32_t const &r)
        {
            std::memcpy(block.data(), l.bytes, 32);
            std::memcpy(block.data() + 32, r.bytes, 32);
        }

        void pack_one_sided(
            block_t &block, bytes32_t const &node, bool const is_right)
        {
            if (is_right) {
                pack_pair(block, bytes32_t{}, node);
            }
            else {
                pack_pair(block, node, bytes32_t{});
            }
        }

        template <size_t MaxMerges>
        void
        merge_many(std::span<block_t const> const blocks, bytes32_t *const out)
        {
            std::array<uint8_t const *, MaxMerges> inputs;
            for (size_t i = 0; i < blocks.size(); ++i) {
                inputs[i] = blocks[i].data();
            }
            blake3_hash_many(
                inputs.data(),
                blocks.size(),
                1,
                IV,
                0,
                false,
                0,
                CHUNK_START,
                CHUNK_END,
                reinterpret_cast<uint8_t *>(out));
        }

        // Each merge makes a distinct parent, so a level has at most half
        // the fanout of them.
        template <unsigned IndexBits>
        Commitment reduce(
            std::array<Commitment, size_t{1} << IndexBits> &level,
            std::array<uint16_t, size_t{1} << IndexBits> &idx, size_t n)
        {
            constexpr size_t MAX_MERGES = (size_t{1} << IndexBits) / 2;
            std::array<block_t, MAX_MERGES> blocks;
            std::array<bytes32_t, MAX_MERGES> out;
            std::array<size_t, MAX_MERGES> merged_at;
            for (unsigned d = 0; d < IndexBits; ++d) {
                if (n == 1 && level[0].is_leaf()) {
                    break;
                }
                size_t merges = 0;
                size_t w = 0;
                size_t i = 0;
                while (i < n) {
                    idx[w] = idx[i];
                    bool const siblings =
                        i + 1 < n &&
                        (idx[i] >> (d + 1)) == (idx[i + 1] >> (d + 1));
                    if (siblings) {
                        pack_pair(
                            blocks[merges],
                            level[i].hash(),
                            level[i + 1].hash());
                        merged_at[merges++] = w;
                        i += 2;
                    }
                    else if (level[i].is_leaf()) {
                        level[w] = level[i];
                        ++i;
                    }
                    else {
                        pack_one_sided(
                            blocks[merges],
                            level[i].hash(),
                            ((idx[i] >> d) & 1) != 0);
                        merged_at[merges++] = w;
                        ++i;
                    }
                    ++w;
                }
                merge_many<MAX_MERGES>(
                    std::span{blocks}.first(merges), out.data());
                for (size_t m = 0; m < merges; ++m) {
                    level[merged_at[m]] = Commitment::internal(out[m]);
                }
                n = w;
            }
            MONAD_ASSERT(n == 1);
            return level[0];
        }
    }

    Commitment
    Commitment::from_child_data(byte_string_view const data, bool const is_leaf)
    {
        MONAD_ASSERT(data.size() == sizeof(bytes32_t));
        return Commitment{to_bytes(data), is_leaf};
    }

    namespace detail
    {
        bytes32_t merge_hash(bytes32_t const &left, bytes32_t const &right)
        {
            block_t block;
            pack_pair(block, left, right);
            return compress_block(IV, block, 0);
        }

        bytes32_t leaf_commit(NibblesView const key, bytes32_t const &value)
        {
            MONAD_ASSERT(key.nibble_size() <= KEY_NIBBLES);
            block_t block{};
            for (unsigned i = 0; i < key.nibble_size(); ++i) {
                auto const nibble = static_cast<uint8_t>(key.get(i));
                block[i / 2] |=
                    static_cast<uint8_t>(i % 2 == 0 ? nibble << 4 : nibble);
            }
            std::memcpy(block.data() + 32, value.bytes, 32);
            return compress_block(leaf_iv(), block, key.nibble_size());
        }
    }

    Commitment merge(Commitment const &left, Commitment const &right)
    {
        return Commitment::internal(
            detail::merge_hash(left.hash(), right.hash()));
    }

    Commitment
    merge_one_sided(Commitment const &child, bool const child_is_right)
    {
        MONAD_ASSERT(!child.is_leaf());
        block_t block;
        pack_one_sided(block, child.hash(), child_is_right);
        return Commitment::internal(compress_block(IV, block, 0));
    }

    Commitment commit_leaf(NibblesView const key, bytes32_t const &value)
    {
        return Commitment::leaf(detail::leaf_commit(key, value));
    }

    template <unsigned IndexBits>
        requires(IndexBits >= 1 && IndexBits <= 8)
    Commitment branch_commit(std::span<Entry const> const entries)
    {
        constexpr size_t FANOUT = size_t{1} << IndexBits;
        MONAD_ASSERT(!entries.empty() && entries.size() <= FANOUT);
        std::array<Commitment, FANOUT> level;
        std::array<uint16_t, FANOUT> idx;
        for (size_t i = 0; i < entries.size(); ++i) {
            MONAD_ASSERT(entries[i].index < FANOUT);
            MONAD_ASSERT(i == 0 || entries[i - 1].index < entries[i].index);
            level[i] = entries[i].child;
            idx[i] = entries[i].index;
        }
        return reduce<IndexBits>(level, idx, entries.size());
    }

    template Commitment branch_commit<4>(std::span<Entry const>);
    template Commitment branch_commit<8>(std::span<Entry const>);

    Commitment commit_path(NibblesView const path, Commitment const &node)
    {
        MONAD_ASSERT(!node.is_leaf());
        Commitment h = node;
        for (unsigned u = path.nibble_size(); u-- > 0;) {
            auto const unit = static_cast<unsigned>(path.get(u));
            for (unsigned bit = 0; bit < 4; ++bit) {
                h = merge_one_sided(h, ((unit >> bit) & 1) != 0);
            }
        }
        return h;
    }

    bytes32_t value_hash(byte_string_view const value)
    {
        blake3_hasher hasher;
        blake3_hasher_init_keyed(&hasher, value_key());
        blake3_hasher_update(&hasher, value.data(), value.size());
        bytes32_t out;
        blake3_hasher_finalize(&hasher, out.bytes, sizeof(out.bytes));
        return out;
    }
}

MONAD_MPT_NAMESPACE_END
