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

#include <cstring>
#include <limits>

MONAD_NAMESPACE_BEGIN

// TurboRLE's test harness (trle.c) allocates output as len*4/3+1024 for
// encoding, and pads input buffers by 1024 bytes for decoding.  The decoder
// performs speculative wide reads (SIMD/word-aligned) past the logical end
// of the input buffer.  We match these conventions here.
constexpr size_t turbo_rle_overhead = 1024;

byte_string rle_encode(uint8_t const *data, size_t const len)
{
    MONAD_ASSERT(len <= std::numeric_limits<unsigned>::max());
    size_t const max_out = len * 4 / 3 + turbo_rle_overhead;
    byte_string out(max_out, 0);
    unsigned const compressed_len = trlec(
        data,
        static_cast<unsigned>(len),
        reinterpret_cast<unsigned char *>(out.data()));
    MONAD_ASSERT(compressed_len <= max_out);
    out.resize(compressed_len);
    return out;
}

void rle_decode(
    uint8_t const *in, size_t const in_len, uint8_t *out, size_t const out_len)
{
    MONAD_ASSERT(in_len <= std::numeric_limits<unsigned>::max());
    MONAD_ASSERT(out_len <= std::numeric_limits<unsigned>::max());
    if (in_len == out_len || in_len <= 1) {
        trled(
            in,
            static_cast<unsigned>(in_len),
            out,
            static_cast<unsigned>(out_len));
        return;
    }
    byte_string padded(in_len + turbo_rle_overhead, 0);
    std::memcpy(padded.data(), in, in_len);
    trled(
        padded.data(),
        static_cast<unsigned>(in_len),
        out,
        static_cast<unsigned>(out_len));
}

MONAD_NAMESPACE_END
