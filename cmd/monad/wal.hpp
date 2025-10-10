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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/monad/core/monad_block.hpp>

#include <evmc/evmc.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>
#include <variant>

MONAD_NAMESPACE_BEGIN

struct MonadChain;

enum class WalAction : uint8_t
{
    PROPOSE = 0,
    FINALIZE = 1,
};

static_assert(sizeof(WalAction) == 1);
static_assert(alignof(WalAction) == 1);

struct WalEntry
{
    WalAction action;
    bytes32_t id;
};

static_assert(sizeof(WalEntry) == 33);
static_assert(alignof(WalEntry) == 1);

class WalReader
{
    MonadChain const &chain_;
    std::ifstream cursor_;
    std::filesystem::path ledger_dir_;
    std::filesystem::path header_dir_;
    std::filesystem::path bodies_dir_;

public:
    struct Result
    {
        WalAction action;
        bytes32_t block_id;
        std::variant<
            MonadConsensusBlockHeaderV0, MonadConsensusBlockHeaderV1,
            MonadConsensusBlockHeaderV2>
            header;
        MonadConsensusBlockBody body;
    };

    WalReader(MonadChain const &, std::filesystem::path const &ledger_dir);

    std::optional<Result> next();
};

class WalWriter
{
    std::filesystem::path wal_path_;
    std::ofstream cursor_;

public:
    WalWriter(std::filesystem::path const &ledger_dir);

    void write(WalAction action, bytes32_t const &block_id);
};

MONAD_NAMESPACE_END
