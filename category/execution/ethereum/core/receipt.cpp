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
#include <category/execution/ethereum/core/chain_hash.hpp>
#include <category/execution/ethereum/core/receipt.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

void set_3_bits(Receipt::Bloom &bloom, byte_string_view const bytes)
{
    // YP Eqn 29, under the chain's bloom hash (chain_hash.hpp).
    auto const hash = bloom_hash(bytes);
    // The three 16-bit big-endian chunks are the hash's first six bytes, so
    // one 64-bit big-endian load holds them all, chunk i at bit 48 - 16i.
    uint64_t const chunks = load_be_unsafe<uint64_t>(hash.bytes);
    for (unsigned i = 0; i < 3; ++i) {
        uint64_t const bit = (chunks >> (48 - 16 * i)) & 2047u;
        bloom[255u - bit / 8u] |= static_cast<unsigned char>(1u << (bit & 7u));
    }
}

void populate_bloom(Receipt::Bloom &bloom, Receipt::Log const &log)
{
    // YP Eqn 28
    set_3_bits(bloom, to_byte_string_view(log.address.bytes));
    for (auto const &i : log.topics) {
        set_3_bits(bloom, to_byte_string_view(i.bytes));
    }
}

void Receipt::add_log(Receipt::Log const &log)
{
    logs.push_back(log);
    populate_bloom(bloom, log);
}

MONAD_NAMESPACE_END
