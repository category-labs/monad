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

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/monad/db/storage_page.hpp>

MONAD_NAMESPACE_BEGIN

// ── Shared RLP layer ────────────────────────────────────────────────
//
// Both encoding formats wrap [key, payload] in an RLP list.  The RLP
// unwrap is the same regardless of the inner value format.

Result<std::pair<bytes32_t, byte_string_view>>
decode_storage_db(byte_string_view &);

// ── Eth single-slot encoding ────────────────────────────────────────
//
// The value is stored as a compact bytes32 (leading zeros stripped).
// DB format: RLP([compact(key), compact(val)])

byte_string encode_storage_eth_db(bytes32_t const &key, bytes32_t const &val);

inline byte_string encode_storage_eth(bytes32_t const &val)
{
    auto const zv = rlp::zeroless_view(to_byte_string_view(val.bytes));
    return byte_string{zv.begin(), zv.end()};
}

inline bytes32_t decode_storage_eth(byte_string_view enc)
{
    if (enc.empty()) {
        return {};
    }
    return to_bytes(enc);
}

// ── Monad page encoding (COO / bitmap) ──────────────────────────────
//
// k < 16 non-zero slots  →  COO:    [0|k](1B) [indices](kB) [values](k×32B)
// k >= 16                →  Bitmap: [1|0](1B) [128-bit mask](16B)
// [values](k×32B)
//
// DB format: RLP([compact(key), string(encode_storage_page(page))])
//
// encode_storage_page / decode_storage_page live in storage_page.hpp.

byte_string
encode_storage_page_db(bytes32_t const &key, storage_page_t const &page);

MONAD_NAMESPACE_END
