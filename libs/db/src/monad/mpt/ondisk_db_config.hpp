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
    bool rewind_to_latest_finalized{false};
    unsigned rd_buffers{1024};
    unsigned wr_buffers{4};
    unsigned uring_entries{512};
    std::optional<unsigned> sq_thread_cpu{0};
    std::optional<uint64_t> start_block_id{std::nullopt};
    std::vector<std::filesystem::path> dbname_paths{};
    std::filesystem::path io_logger_path{};
    int64_t file_size_db{512}; // truncate files to this size
    unsigned concurrent_read_io_limit{1024};
    // fixed history length if contains value, otherwise rely on db to adjust
    // history length upon disk usage
    std::optional<uint64_t> fixed_history_length{std::nullopt};
};

struct ReadOnlyOnDiskDbConfig
{
    bool disable_mismatching_storage_pool_check{
        false}; // risk of severe data loss
    bool capture_io_latencies{false};
    bool eager_completions{false};
    unsigned rd_buffers{1024};
    unsigned uring_entries{128};
    // default to disable sqpoll kernel thread since now ReadOnlyDb uses
    // blocking read
    std::optional<unsigned> sq_thread_cpu{std::nullopt};
    std::vector<std::filesystem::path> dbname_paths;
    std::filesystem::path io_logger_path{};
    unsigned concurrent_read_io_limit{600};
    unsigned node_lru_size{102400};
};

MONAD_MPT_NAMESPACE_END
