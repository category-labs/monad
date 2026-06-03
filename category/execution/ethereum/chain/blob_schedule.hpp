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

#pragma once

#include <category/core/config.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct BlobSchedule
{
    uint64_t target_blobs_per_block;
    uint64_t max_blobs_per_block;
    uint64_t blob_base_fee_update_fraction;
};

inline constexpr BlobSchedule CANCUN_BLOB_SCHEDULE{
    .target_blobs_per_block = 3,
    .max_blobs_per_block = 6,
    .blob_base_fee_update_fraction = 3'338'477};

inline constexpr BlobSchedule PRAGUE_BLOB_SCHEDULE{
    .target_blobs_per_block = 6,
    .max_blobs_per_block = 9,
    .blob_base_fee_update_fraction = 5'007'716};

inline constexpr BlobSchedule BPO1_BLOB_SCHEDULE{
    .target_blobs_per_block = 10,
    .max_blobs_per_block = 15,
    .blob_base_fee_update_fraction = 8'346'193};

inline constexpr BlobSchedule BPO2_BLOB_SCHEDULE{
    .target_blobs_per_block = 14,
    .max_blobs_per_block = 21,
    .blob_base_fee_update_fraction = 11'684'671};

MONAD_NAMESPACE_END
