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

#include <category/execution/ethereum/process_requests.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

using namespace monad;

namespace
{
    using monad::literals::operator""_bytes;

    // EIP-7685 requests_hash test vectors:
    // sha256(concat(sha256(request_type || request_data).digest())).
    // Expected values were generated independently with Python hashlib.sha256
    // for: [], [(0x01, aabbcc)], [(0x02, aabbcc)], [(0x01, 00..7f)],
    // [(0x01, 1122), (0x02, 3344)], and the reversed order.
    constexpr auto EMPTY_REQUESTS_HASH =
        0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855_bytes32;
    constexpr auto WITHDRAWAL_AABBCC_REQUESTS_HASH =
        0x8053cefe887c01df53ed249a88f280c4a550f84faf7363d29acaad6b57b0c4eb_bytes32;
    constexpr auto CONSOLIDATION_AABBCC_REQUESTS_HASH =
        0xce00379bd99b3739955f6375984912eb0f18027bf935a056cc03167161007e2d_bytes32;
    constexpr auto LARGE_0X01_REQUESTS_HASH =
        0xb371760f13b3feadb186aaf03d8723138b3316bb1ce1d18d6ce1385cde8f3828_bytes32;
    constexpr auto ORDERED_0X01_0X02_REQUESTS_HASH =
        0x1bfdf42ee5c7c1cf68be7759dc298f49ff824ceea15be154dedd2d40822de069_bytes32;
    constexpr auto REVERSED_0X02_0X01_REQUESTS_HASH =
        0x00a28f3139e5ac6a7c8aa970bce5488f9669e3f5db94205291b6bf9772478bf0_bytes32;
}

TEST(ProcessRequests, EmptyRequestListHash)
{
    EXPECT_EQ(
        compute_requests_hash(std::span<BlockRequest const>{}),
        EMPTY_REQUESTS_HASH);
}

TEST(ProcessRequests, EmptyRequestDataIsSkipped)
{
    auto const withdrawal_data = 0xaabbcc_bytes;
    std::array<BlockRequest, 2> const requests{{
        {0x00, {}},
        {0x01, withdrawal_data},
    }};

    EXPECT_EQ(compute_requests_hash(requests), WITHDRAWAL_AABBCC_REQUESTS_HASH);
}

TEST(ProcessRequests, RequestTypeParticipatesInHash)
{
    auto const data = 0xaabbcc_bytes;
    std::array<BlockRequest, 1> const withdrawal_requests{{
        {0x01, data},
    }};
    std::array<BlockRequest, 1> const consolidation_requests{{
        {0x02, data},
    }};

    EXPECT_EQ(
        compute_requests_hash(withdrawal_requests),
        WITHDRAWAL_AABBCC_REQUESTS_HASH);
    EXPECT_EQ(
        compute_requests_hash(consolidation_requests),
        CONSOLIDATION_AABBCC_REQUESTS_HASH);
    EXPECT_NE(
        compute_requests_hash(withdrawal_requests),
        compute_requests_hash(consolidation_requests));
}

TEST(ProcessRequests, HashesFullRequestPayload)
{
    byte_string large_data(128, uint8_t{0});
    for (std::size_t i = 0; i < large_data.size(); ++i) {
        large_data[i] = static_cast<uint8_t>(i);
    }

    std::array<BlockRequest, 1> const requests{{
        {0x01, large_data},
    }};

    EXPECT_EQ(compute_requests_hash(requests), LARGE_0X01_REQUESTS_HASH);
}

TEST(ProcessRequests, NoncanonicalRequestOrderIsPreserved)
{
    auto const withdrawal_data = 0x1122_bytes;
    auto const consolidation_data = 0x3344_bytes;
    std::array<BlockRequest, 2> const ordered_requests{{
        {0x01, withdrawal_data},
        {0x02, consolidation_data},
    }};
    std::array<BlockRequest, 2> const reversed_requests{{
        {0x02, consolidation_data},
        {0x01, withdrawal_data},
    }};

    // Canonical block request lists are ordered by ascending request type, but
    // the hash helper does not sort or normalize caller input.
    EXPECT_EQ(
        compute_requests_hash(ordered_requests),
        ORDERED_0X01_0X02_REQUESTS_HASH);
    EXPECT_EQ(
        compute_requests_hash(reversed_requests),
        REVERSED_0X02_0X01_REQUESTS_HASH);
    EXPECT_NE(
        compute_requests_hash(ordered_requests),
        compute_requests_hash(reversed_requests));
}
