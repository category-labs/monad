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

#include <category/core/assert.h>
#include <category/execution/ethereum/db/rle.hpp>

extern "C"
{
#include <trle.h>
}

#include <limits>

MONAD_NAMESPACE_BEGIN

byte_string rle_encode(uint8_t const *data, size_t const len)
{
    MONAD_ASSERT(len <= std::numeric_limits<unsigned>::max());
    size_t const max_out = len + (len / 64) + 2;
    byte_string out(max_out, 0);
    unsigned const compressed_len = trlec(
        data,
        static_cast<unsigned>(len),
        reinterpret_cast<unsigned char *>(out.data()));
    out.resize(compressed_len);
    return out;
}

void rle_decode(
    uint8_t const *in, size_t const in_len, uint8_t *out, size_t const out_len)
{
    MONAD_ASSERT(in_len <= std::numeric_limits<unsigned>::max());
    MONAD_ASSERT(out_len <= std::numeric_limits<unsigned>::max());
    trled(
        in, static_cast<unsigned>(in_len), out, static_cast<unsigned>(out_len));
}

MONAD_NAMESPACE_END
