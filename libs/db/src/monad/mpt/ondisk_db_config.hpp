#pragma once

#include <monad/mpt/config.hpp>

#include <filesystem>
#include <optional>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

struct StateMachine;

struct OnDiskDbConfig
{
    bool append{false};
    bool compaction{false};
    bool enable_io_polling{false};
    bool capture_io_latencies{false};
    bool eager_completions{false};
    unsigned rd_buffers{1024};
    unsigned wr_buffers{4};
    unsigned uring_entries{512};
    std::optional<unsigned> sq_thread_cpu{0};
    std::optional<uint64_t> start_block_id{std::nullopt};
    std::vector<std::filesystem::path> dbname_paths{};
    int64_t file_size_db{512}; // truncate files to this size
    unsigned concurrent_read_io_limit{1024};
    uint64_t history_length{1000};
};

struct ReadOnlyOnDiskDbConfig
{
    bool disable_mismatching_storage_pool_check{
        false}; // risk of severe data loss
    bool capture_io_latencies{false};
    bool eager_completions{false};
    unsigned rd_buffers{128};
    unsigned uring_entries{128};
    // default to disable sqpoll kernel thread since now ReadOnlyDb uses
    // blocking read
    std::optional<unsigned> sq_thread_cpu{std::nullopt};
    std::vector<std::filesystem::path> dbname_paths;
    unsigned concurrent_read_io_limit{1024};
};

MONAD_MPT_NAMESPACE_END
