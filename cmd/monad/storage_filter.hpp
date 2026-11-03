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
#include <category/execution/ethereum/db/storage_filter.hpp>

#include <atomic>
#include <cstddef>
#include <filesystem>
#include <memory>
#include <optional>
#include <thread>

MONAD_NAMESPACE_BEGIN

class TrieDb;

namespace mpt
{
    class Db;
}

struct StorageFilterOptions
{
    std::optional<size_t> size_mb; // default: StorageFilter::default_config
    std::optional<unsigned> num_probes;
    std::filesystem::path file; // empty: neither loaded nor saved
    unsigned build_threads{4};
    bool wait_for_build{false};
};

// The storage filter of one execution run. On construction it loads the
// filter from the options' file if that holds one for the db's starting
// state, else builds it from the db, in the background unless asked to wait,
// and attaches it to the TrieDb before the first block executes. On
// destruction it stops an unfinished build and saves a complete filter for
// the latest finalized block.
class StorageFilterSetup
{
    mpt::Db &db_;
    std::filesystem::path dbname_path_;
    std::filesystem::path file_;
    std::shared_ptr<StorageFilter> filter_;
    std::atomic<bool> stop_{false};
    std::thread builder_;

    void build(StorageFilterTag const &, unsigned num_threads);

public:
    StorageFilterSetup(
        mpt::Db &, TrieDb &, std::filesystem::path const &dbname_path,
        StorageFilterOptions const &);
    ~StorageFilterSetup();

    StorageFilterSetup(StorageFilterSetup const &) = delete;
    StorageFilterSetup &operator=(StorageFilterSetup const &) = delete;
};

MONAD_NAMESPACE_END
