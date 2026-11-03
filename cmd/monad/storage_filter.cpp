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

#include "storage_filter.hpp"

#include <category/core/config.hpp>
#include <category/core/log.hpp>
#include <category/execution/ethereum/db/storage_filter.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/mpt/db.hpp>

#include <quill/std/Chrono.h>
#include <quill/std/FilesystemPath.h>

#include <atomic>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <memory>
#include <optional>
#include <thread>

MONAD_NAMESPACE_BEGIN

StorageFilterSetup::StorageFilterSetup(
    mpt::Db &db, TrieDb &triedb, std::filesystem::path const &dbname_path,
    StorageFilterOptions const &options)
    : db_{db}
    , dbname_path_{dbname_path}
    , file_{options.file}
{
    bool const page_encoded = triedb.is_page_encoded();
    auto config = StorageFilter::default_config(page_encoded);
    if (options.size_mb.has_value()) {
        config.size_bytes = options.size_mb.value() << 20;
    }
    if (options.num_probes.has_value()) {
        config.num_probes = options.num_probes.value();
    }
    uint64_t const base = triedb.get_block_number();
    auto const tag = finalized_storage_filter_tag(db_, base, page_encoded);
    if (!tag.has_value()) {
        LOG_WARNING(
            "storage filter: disabled, block {} has no finalized state in the "
            "db",
            base);
        return;
    }
    if (!file_.empty()) {
        filter_ = StorageFilter::load(file_, tag.value(), config);
    }
    if (filter_) {
        // Saved filters keep growing with the state and keep the leaves that
        // were deleted; only a larger filter brings the rate back down
        double const rate = filter_->bloom().false_positive_rate();
        if (rate > 0.01) {
            LOG_WARNING(
                "storage filter: estimated false positive rate {:.3e}; a "
                "larger --storage-filter-mb would answer more reads",
                rate);
        }
        else {
            LOG_INFO(
                "storage filter: estimated false positive rate {:.3e}", rate);
        }
    }
    else {
        filter_ = std::make_shared<StorageFilter>(config, page_encoded, base);
        if (options.wait_for_build) {
            build(tag.value(), options.build_threads);
        }
        else {
            builder_ = std::thread{
                [this, tag = tag.value(), threads = options.build_threads] {
                    build(tag, threads);
                }};
        }
    }
    // Before the first block, so that every block from the base on inserts
    // the leaves it creates, also while a background build runs
    triedb.set_storage_filter(filter_);
}

void StorageFilterSetup::build(
    StorageFilterTag const &tag, unsigned const num_threads)
{
    LOG_INFO(
        "storage filter: building from block {} with {} threads, {} MiB, {} "
        "probes",
        tag.block_number,
        num_threads,
        filter_->bloom().size_bytes() >> 20,
        filter_->bloom().num_probes());
    auto const start = std::chrono::steady_clock::now();
    auto const leaves = build_storage_filter(
        *filter_, dbname_path_, tag.block_number, num_threads, &stop_);
    if (!leaves.has_value()) {
        LOG_WARNING(
            "storage filter: build from block {} did not complete; storage "
            "reads will not use the filter",
            tag.block_number);
        return;
    }
    filter_->set_ready();
    LOG_INFO(
        "storage filter: built from block {}: {} leaves in {}, estimated "
        "false positive rate {:.3e}",
        tag.block_number,
        leaves.value(),
        std::chrono::duration_cast<std::chrono::seconds>(
            std::chrono::steady_clock::now() - start),
        filter_->bloom().false_positive_rate());
    if (!file_.empty()) {
        (void)filter_->save(file_, tag);
    }
}

StorageFilterSetup::~StorageFilterSetup()
{
    stop_.store(true, std::memory_order_relaxed);
    if (builder_.joinable()) {
        builder_.join();
    }
    if (!filter_ || !filter_->is_ready() || file_.empty()) {
        return;
    }
    // Every block committed so far inserted its leaves, so the filter is
    // complete for the latest finalized state
    uint64_t const finalized = db_.get_latest_finalized_version();
    if (finalized < filter_->base_block_number()) {
        return;
    }
    auto const tag = finalized_storage_filter_tag(
        db_, finalized, filter_->is_page_encoded());
    if (tag.has_value()) {
        (void)filter_->save(file_, tag.value());
    }
}

MONAD_NAMESPACE_END
