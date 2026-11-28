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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/storage_page.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <random>

using namespace monad;

// encode_account_db, encode_storage_db and encode_storage_page_db each write
// their value in a single allocation. The references below build the same
// values field by field from the RLP field encoders, so these tests pin the
// bytes that feed the state root.
namespace
{
    byte_string ref_account_db(Address const &address, Account const &account)
    {
        byte_string fields;
        fields += rlp::encode_address(address);
        fields += rlp::encode_unsigned(account.incarnation.to_int());
        fields += rlp::encode_unsigned(account.nonce);
        fields += rlp::encode_unsigned(account.balance);
        if (account.code_hash != NULL_HASH) {
            fields += rlp::encode_bytes32(account.code_hash);
        }
        return rlp::encode_list2(fields);
    }

    byte_string ref_storage_db(bytes32_t const &key, bytes32_t const &val)
    {
        byte_string fields;
        fields += rlp::encode_bytes32_compact(key);
        fields += rlp::encode_bytes32_compact(val);
        return rlp::encode_list2(fields);
    }

    byte_string ref_storage_page(storage_page_t const &page)
    {
        byte_string encoded;
        auto const values = page.values();
        size_t dense = 0;
        for (auto bits = page.bitmap(); bits != 0; bits &= bits - 1) {
            encoded.push_back(lowest_offset(bits));
            encoded += rlp::encode_bytes32_compact(values[dense]);
            ++dense;
        }
        return encoded;
    }

    byte_string
    ref_storage_page_db(bytes32_t const &key, storage_page_t const &page)
    {
        return rlp::encode_list2(
            rlp::encode_bytes32_compact(key),
            rlp::encode_string2(ref_storage_page(page)));
    }

    // Zero, lone bytes either side of 0x80, and big-endian values of every
    // length up to 32 bytes.
    bytes32_t random_word(std::mt19937_64 &rng)
    {
        bytes32_t w{};
        switch (rng() % 5) {
        case 0:
            break;
        case 1:
            w.bytes[31] = static_cast<uint8_t>(rng() % 0x80);
            break;
        case 2:
            w.bytes[31] = static_cast<uint8_t>(0x80 + rng() % 0x80);
            break;
        default:
            for (size_t i = 32 - (1 + rng() % 32); i < 32; ++i) {
                w.bytes[i] = static_cast<uint8_t>(rng());
            }
        }
        return w;
    }

    uint64_t random_u64(std::mt19937_64 &rng)
    {
        return rng() >> (rng() % 64);
    }
}

TEST(EncodeDb, account_matches_field_composition)
{
    std::mt19937_64 rng{1};
    for (int i = 0; i < 20000; ++i) {
        Address address;
        for (auto &b : address.bytes) {
            b = static_cast<uint8_t>(rng());
        }
        Account account;
        account.nonce = random_u64(rng);
        account.balance =
            uint256_t{
                random_u64(rng),
                random_u64(rng),
                random_u64(rng),
                random_u64(rng)} >>
            (rng() % 256);
        account.incarnation = Incarnation{
            random_u64(rng) % (1ull << 40), random_u64(rng) % (1ull << 24)};
        account.code_hash = rng() % 3 == 0 ? NULL_HASH : random_word(rng);
        ASSERT_EQ(
            encode_account_db(address, account),
            ref_account_db(address, account))
            << "iteration " << i;
    }
}

TEST(EncodeDb, storage_matches_field_composition)
{
    std::mt19937_64 rng{2};
    for (int i = 0; i < 20000; ++i) {
        bytes32_t const key = random_word(rng);
        bytes32_t const val = random_word(rng);
        ASSERT_EQ(encode_storage_db(key, val), ref_storage_db(key, val))
            << "iteration " << i;
    }
}

TEST(EncodeDb, storage_page_matches_field_composition)
{
    std::mt19937_64 rng{3};
    for (int i = 0; i < 5000; ++i) {
        storage_page_t page;
        size_t const fill = rng() % (storage_page_t::SLOTS + 1);
        for (size_t s = 0; s < fill; ++s) {
            bytes32_t v = random_word(rng);
            v.bytes[0] |= static_cast<uint8_t>(rng() % 2);
            page.set(static_cast<uint8_t>(rng() % storage_page_t::SLOTS), v);
        }
        bytes32_t const key = random_word(rng);
        ASSERT_EQ(encode_storage_page(page), ref_storage_page(page))
            << "iteration " << i;
        ASSERT_EQ(
            encode_storage_page_db(key, page), ref_storage_page_db(key, page))
            << "iteration " << i << ", " << page.size() << " values";
    }
}
