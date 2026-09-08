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
#include <category/core/config.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/rpc/utils/value_size.hpp>

#include <bit>
#include <cstddef>
#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

size_t value_size(size_t x)
{
    // The image of bit_width is [0, 64] for size_t on typical platforms, so it
    // is safe to interpret its return value as an element of size_t.
    return x == 0 ? 3 : 2 + (static_cast<size_t>(std::bit_width(x)) + 3) / 4;
}

size_t value_size(uint256_t const &x)
{
    return x == 0 ? 3 : 2 + (monad::bit_width(x) + 3) / 4;
}

size_t value_size(Address const &)
{
    return 2 * sizeof(Address) + 2 /* 0xABCDEF.... */;
}

size_t value_size(bytes32_t const &)
{
    return 2 * sizeof(bytes32_t) + 2 /* 0xABCDEF.... */;
}

size_t value_size(byte_string_view const &x)
{
    return x.size() * 2 + 2 /* 0xABCDEF.... */;
}

size_t value_size(byte_string const &x)
{
    return x.size() * 2 + 2 /* 0xABCDEF.... */;
}

size_t value_size(byte_string_fixed<8> const &)
{
    return 18; // 0x0000...
}

size_t value_size(byte_string_fixed<256> const &)
{
    return 514; // 0x0000...
}

size_t value_size(std::optional<Address> const &x)
{
    if (x.has_value()) {
        return value_size(x.value());
    }
    else {
        return 3; // 0x0
    }
}

size_t value_size(std::optional<bytes32_t> const &x)
{
    if (x.has_value()) {
        return value_size(x.value());
    }
    else {
        return 3; // 0x0
    }
}

size_t value_size(std::optional<uint64_t> const &x)
{
    if (x.has_value()) {
        return value_size(x.value());
    }
    else {
        return 3; // 0x0
    }
}

size_t value_size(std::optional<uint256_t> const &x)
{
    if (x.has_value()) {
        return value_size(x.value());
    }
    else {
        return 3; // 0x0
    }
}

size_t padded_max_size(size_t max_size)
{
    // We use the size of the in-memory structures to bound the memory
    // consumption. This estimator is inaccurate as the RPC
    // client submits the maximum size of the CBOR response, which is
    // more compact than the in-memory structures.  Therefore we keep a
    // small amount of headroom to absorb estimator drift while still
    // bounding memory growth. We use a monotonic hyperbolic function to
    // compute the headroom, which decays percentage-wise as the
    // `max_size` increases. This is to avoid over-estimating the
    // headroom for large `max_size` values, preventing excessive
    // memory usage.
    //
    // Monotonic hyperbolic percentage in basis points:
    // S(M) = M_min + (M_max - M_min) * k / (k + M)
    // where k controls how quickly slack decays.
    constexpr size_t bps_scale = 10'000; // basis points: 100% = 10'000.
    constexpr size_t M_max = bps_scale / 2; // 50%
    constexpr size_t M_min = 1; // 0.01%
    constexpr size_t k = 4096; // 4 KiB
    // At the time of writing the BFT RPC client has M = 25'000'000 (25
    // MB). Meaning, we get roughly 2500 bytes of slack using this
    // method.

    size_t const denominator = max_size > std::numeric_limits<size_t>::max() - k
                                   ? std::numeric_limits<size_t>::max()
                                   : max_size + k;
    size_t const slack_bps = M_min + ((M_max - M_min) * k) / denominator;

    // Computing `ceil(max_size * slack_bps / bps_scale)` using integer
    // maths.
    size_t const whole = (max_size / bps_scale) * slack_bps;
    size_t const remainder = max_size % bps_scale;
    size_t const fraction =
        (remainder * slack_bps + (bps_scale - 1)) / bps_scale;
    size_t const slack = whole + fraction;

    if (max_size > std::numeric_limits<size_t>::max() - slack) {
        return std::numeric_limits<size_t>::max();
    }
    return max_size + slack;
}

MONAD_NAMESPACE_END
