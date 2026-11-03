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
#include <category/execution/monad/core/domain_block.hpp>

#include <cstdint>
#include <filesystem>
#include <optional>

MONAD_NAMESPACE_BEGIN

// One private domain's finalized blocks, in order from genesis, in a
// directory of its own:
//   blocks/<number / blocks_per_directory>/<number>: rlp(DomainBlock)
//   cursor: the last L1 block derived, in decimal
// The cursor is kept apart from the blocks because most L1 blocks yield no
// domain block. Every file is written to a temporary file, synced and
// renamed into place, so a crash leaves either the old file or the new one.
// A corrupt store aborts.
class DomainBlockStore
{
    std::filesystem::path dir_;
    uint64_t blocks_per_directory_;
    std::optional<DomainBlock> tip_;
    std::optional<uint64_t> l1_cursor_;

    std::filesystem::path block_path(uint64_t number) const;

public:
    // Opens the store in `dir`, creating it if needed.
    explicit DomainBlockStore(
        std::filesystem::path dir, uint64_t blocks_per_directory = 10'000);

    // The last block appended, nullopt while the store is empty.
    std::optional<DomainBlock> const &tip() const
    {
        return tip_;
    }

    std::optional<DomainBlock> get(uint64_t number) const;

    // Appends the block after the tip, or block 0 to an empty store.
    void append(DomainBlock const &);

    // The last L1 block derived, nullopt before the first.
    std::optional<uint64_t> l1_cursor() const
    {
        return l1_cursor_;
    }

    void set_l1_cursor(uint64_t);
};

MONAD_NAMESPACE_END
