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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/db/partitioned_layout.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <algorithm>
#include <bit>
#include <cstring>

MONAD_NAMESPACE_BEGIN

namespace partitioned
{
    namespace
    {
        using Address32 = std::array<unsigned char, 32>;

        Address32 address32_bytes(Address const &address)
        {
            Address32 ret{};
            std::memcpy(ret.data() + 12, address.bytes, sizeof(address.bytes));
            return ret;
        }

        bytes32_t index32(uint64_t const index)
        {
            return store_be_as<bytes32_t>(uint256_t{index});
        }

        template <size_t N>
        bytes32_t hash_concat(
            std::array<unsigned char, N> const &prefix, bytes32_t const &suffix)
        {
            std::array<unsigned char, N + 32> buf;
            std::memcpy(buf.data(), prefix.data(), N);
            std::memcpy(buf.data() + N, suffix.bytes, 32);
            return key_hash({buf.data(), buf.size()});
        }

        void store_be_n(unsigned char *const dest, size_t const n, uint64_t v)
        {
            for (size_t i = n; i-- > 0;) {
                dest[i] = static_cast<unsigned char>(v & 0xff);
                v >>= 8;
            }
        }

        uint64_t load_be_n(unsigned char const *const src, size_t const n)
        {
            uint64_t v = 0;
            for (size_t i = 0; i < n; ++i) {
                v = (v << 8) | src[i];
            }
            return v;
        }
    }

    bytes32_t key_hash(byte_string_view const input)
    {
        return to_bytes(state_key_hash(input));
    }

    bytes32_t address32(Address const &address)
    {
        auto const a = address32_bytes(address);
        return to_bytes(byte_string_view{a.data(), a.size()});
    }

    bytes32_t address_position(Address const &address)
    {
        auto const a = address32_bytes(address);
        return key_hash({a.data(), a.size()});
    }

    bytes32_t
    storage_page_position(Address const &address, bytes32_t const &page_key)
    {
        return hash_concat(address32_bytes(address), page_key);
    }

    bytes32_t
    code_group_position(bytes32_t const &code_hash, uint64_t const group)
    {
        std::array<unsigned char, 32> h;
        std::memcpy(h.data(), code_hash.bytes, 32);
        return hash_concat(h, index32(group));
    }

    Stem header_stem(Address const &address)
    {
        Stem stem;
        stem[0] = ACCOUNT_ZONE;
        std::memcpy(stem.data() + 1, address_position(address).bytes, 32);
        return stem;
    }

    AccountKey header_key(Address const &address, uint8_t const sub_index)
    {
        AccountKey key;
        auto const stem = header_stem(address);
        std::memcpy(key.data(), stem.data(), stem.size());
        key[STEM_LENGTH] = sub_index;
        return key;
    }

    Stem storage_stem(Address const &address)
    {
        Stem stem;
        stem[0] = STORAGE_ZONE;
        std::memcpy(stem.data() + 1, address_position(address).bytes, 32);
        return stem;
    }

    CodeKey code_chunk_key(bytes32_t const &code_hash, uint64_t const chunk_id)
    {
        CodeKey key;
        key[0] = CODE_ZONE;
        std::memcpy(
            key.data() + 1,
            code_group_position(code_hash, chunk_id / STEM_SUBTREE_WIDTH).bytes,
            32);
        key[STEM_LENGTH] = static_cast<uint8_t>(chunk_id % STEM_SUBTREE_WIDTH);
        return key;
    }

    StorageLocation locate_storage(bytes32_t const &slot)
    {
        return StorageLocation{
            .page_key = compute_page_key(slot),
            .offset = compute_slot_offset(slot)};
    }

    bool is_header_slot(bytes32_t const &slot)
    {
        return std::all_of(
                   slot.bytes,
                   slot.bytes + 31,
                   [](unsigned char const b) { return b == 0; }) &&
               slot.bytes[31] < HEADER_STORAGE_SLOTS;
    }

    uint8_t header_slot_offset(bytes32_t const &slot)
    {
        MONAD_ASSERT(is_header_slot(slot));
        return slot.bytes[31];
    }

    byte_string storage_key(Address const &address, bytes32_t const &slot)
    {
        auto const loc = locate_storage(slot);
        if (loc.in_header()) {
            auto const key = header_key(address, BASIC_DATA_LEAF_KEY);
            return byte_string{key.data(), key.size()};
        }
        StorageKey key;
        auto const stem = storage_stem(address);
        std::memcpy(key.data(), stem.data(), stem.size());
        std::memcpy(
            key.data() + STEM_LENGTH,
            storage_page_position(address, loc.page_key).bytes,
            32);
        return byte_string{key.data(), key.size()};
    }

    mpt::Nibbles zone_nibbles(unsigned char const zone)
    {
        return mpt::concat(mpt::NibblesView{byte_string_view{&zone, 1}});
    }

    mpt::Nibbles sub_index_nibbles(uint8_t const sub_index)
    {
        unsigned char const b = sub_index;
        return mpt::concat(mpt::NibblesView{byte_string_view{&b, 1}});
    }

    mpt::Nibbles hash_nibbles(bytes32_t const &hash)
    {
        return mpt::concat(mpt::NibblesView{to_byte_string_view(hash.bytes)});
    }

    mpt::Nibbles header_stem_nibbles(Address const &address)
    {
        unsigned char const zone = ACCOUNT_ZONE;
        return mpt::concat(
            mpt::NibblesView{byte_string_view{&zone, 1}},
            mpt::NibblesView{
                to_byte_string_view(address_position(address).bytes)});
    }

    mpt::Nibbles storage_stem_nibbles(Address const &address)
    {
        unsigned char const zone = STORAGE_ZONE;
        return mpt::concat(
            mpt::NibblesView{byte_string_view{&zone, 1}},
            mpt::NibblesView{
                to_byte_string_view(address_position(address).bytes)});
    }

    mpt::Nibbles
    header_key_nibbles(Address const &address, uint8_t const sub_index)
    {
        unsigned char const b = sub_index;
        return mpt::concat(
            mpt::NibblesView{header_stem_nibbles(address)},
            mpt::NibblesView{byte_string_view{&b, 1}});
    }

    mpt::Nibbles
    storage_page_key_nibbles(Address const &address, bytes32_t const &page_key)
    {
        return mpt::concat(
            mpt::NibblesView{storage_stem_nibbles(address)},
            mpt::NibblesView{to_byte_string_view(
                storage_page_position(address, page_key).bytes)});
    }

    mpt::Nibbles
    storage_key_nibbles(Address const &address, bytes32_t const &slot)
    {
        auto const loc = locate_storage(slot);
        if (loc.in_header()) {
            return header_stem_nibbles(address);
        }
        return storage_page_key_nibbles(address, loc.page_key);
    }

    mpt::Nibbles
    code_chunk_key_nibbles(bytes32_t const &code_hash, uint64_t const chunk_id)
    {
        unsigned char const zone = CODE_ZONE;
        unsigned char const b =
            static_cast<unsigned char>(chunk_id % STEM_SUBTREE_WIDTH);
        return mpt::concat(
            mpt::NibblesView{byte_string_view{&zone, 1}},
            mpt::NibblesView{to_byte_string_view(
                code_group_position(code_hash, chunk_id / STEM_SUBTREE_WIDTH)
                    .bytes)},
            mpt::NibblesView{byte_string_view{&b, 1}});
    }

    bytes32_t
    encode_basic_data(Account const &account, uint32_t const code_size)
    {
        MONAD_ASSERT_PRINTF(
            (account.balance >> (8 * BASIC_DATA_BALANCE_BYTES)) == 0,
            "balance does not fit the 16 byte basic data field");
        bytes32_t out{};
        out.bytes[BASIC_DATA_VERSION_OFFSET] = 0;
        store_be_n(out.bytes + BASIC_DATA_CODE_SIZE_OFFSET, 4, code_size);
        store_be_n(out.bytes + BASIC_DATA_NONCE_OFFSET, 8, account.nonce);
        auto const balance = store_be_as<bytes32_t>(account.balance);
        std::memcpy(
            out.bytes + BASIC_DATA_BALANCE_OFFSET,
            balance.bytes + 32 - BASIC_DATA_BALANCE_BYTES,
            BASIC_DATA_BALANCE_BYTES);
        return out;
    }

    std::optional<BasicData> decode_basic_data(byte_string_view const value)
    {
        if (value.size() != 32) {
            return std::nullopt;
        }
        unsigned char const *const p = value.data();
        bytes32_t balance{};
        std::memcpy(
            balance.bytes + 32 - BASIC_DATA_BALANCE_BYTES,
            p + BASIC_DATA_BALANCE_OFFSET,
            BASIC_DATA_BALANCE_BYTES);
        return BasicData{
            .version = p[BASIC_DATA_VERSION_OFFSET],
            .code_size = static_cast<uint32_t>(
                load_be_n(p + BASIC_DATA_CODE_SIZE_OFFSET, 4)),
            .nonce = load_be_n(p + BASIC_DATA_NONCE_OFFSET, 8),
            .balance = load_be<uint256_t>(balance)};
    }

    byte_string encode_account_leaf(
        Account const &account, storage_page_t const &header,
        uint32_t const code_size)
    {
        byte_string leaf;
        auto const basic = encode_basic_data(account, code_size);
        leaf.append(basic.bytes, sizeof(basic.bytes));
        leaf.append(account.code_hash.bytes, sizeof(account.code_hash.bytes));
        unsigned char inc[8];
        store_be_n(inc, 8, account.incarnation.to_int());
        leaf.append(inc, sizeof(inc));
        MONAD_ASSERT(leaf.size() == ACCOUNT_FIELDS_LENGTH);
        leaf += encode_storage_page(header);
        return leaf;
    }

    std::optional<AccountLeaf> decode_account_leaf(byte_string_view const leaf)
    {
        if (leaf.size() < ACCOUNT_FIELDS_LENGTH) {
            return std::nullopt;
        }
        auto const basic = decode_basic_data(leaf.substr(0, 32));
        if (!basic.has_value()) {
            return std::nullopt;
        }
        auto page = decode_storage_page(leaf.substr(ACCOUNT_FIELDS_LENGTH));
        if (page.has_error()) {
            return std::nullopt;
        }
        return AccountLeaf{
            .account =
                Account{
                    .balance = basic->balance,
                    .code_hash = to_bytes(leaf.substr(32, 32)),
                    .nonce = basic->nonce,
                    .incarnation =
                        Incarnation::from_int(load_be_n(leaf.data() + 64, 8))},
            .header = std::move(page).value()};
    }

    std::vector<bytes32_t> chunkify_code(byte_string_view const code)
    {
        constexpr unsigned char PUSH_OFFSET = 95;
        constexpr unsigned char PUSH1 = PUSH_OFFSET + 1;
        constexpr unsigned char PUSH32 = PUSH_OFFSET + 32;

        size_t const padded_len = (code.size() + CODE_CHUNK_CODE_BYTES - 1) /
                                  CODE_CHUNK_CODE_BYTES * CODE_CHUNK_CODE_BYTES;
        // bytes_to_exec_data[i]: how many bytes from i on are PUSH data
        std::vector<uint8_t> bytes_to_exec_data(padded_len + 32, 0);
        size_t pos = 0;
        while (pos < code.size()) {
            unsigned const pushdata_bytes =
                (code[pos] >= PUSH1 && code[pos] <= PUSH32)
                    ? code[pos] - PUSH_OFFSET
                    : 0;
            ++pos;
            for (unsigned x = 0; x < pushdata_bytes; ++x) {
                bytes_to_exec_data[pos + x] =
                    static_cast<uint8_t>(pushdata_bytes - x);
            }
            pos += pushdata_bytes;
        }
        std::vector<bytes32_t> chunks;
        chunks.reserve(padded_len / CODE_CHUNK_CODE_BYTES);
        for (size_t i = 0; i < padded_len; i += CODE_CHUNK_CODE_BYTES) {
            bytes32_t chunk{};
            chunk.bytes[0] = static_cast<unsigned char>(std::min<unsigned>(
                bytes_to_exec_data[i], CODE_CHUNK_CODE_BYTES));
            size_t const n = std::min(CODE_CHUNK_CODE_BYTES, code.size() - i);
            std::memcpy(chunk.bytes + 1, code.data() + i, n);
            chunks.push_back(chunk);
        }
        return chunks;
    }

    byte_string unchunkify_code(
        std::vector<std::optional<bytes32_t>> const &chunks,
        size_t const code_size)
    {
        byte_string code(code_size, 0);
        for (size_t i = 0; i < chunks.size(); ++i) {
            if (!chunks[i].has_value()) {
                continue;
            }
            size_t const off = i * CODE_CHUNK_CODE_BYTES;
            if (off >= code_size) {
                break;
            }
            size_t const n = std::min(CODE_CHUNK_CODE_BYTES, code_size - off);
            std::memcpy(code.data() + off, chunks[i]->bytes + 1, n);
        }
        return code;
    }
}

MONAD_NAMESPACE_END
