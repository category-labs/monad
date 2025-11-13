#pragma once

#include <csignal>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <source_location>
#include <string>
#include <utility>

#include <fcntl.h>
#include <sys/types.h>
#include <syslog.h>

struct monad_bcap_archive;

extern std::sig_atomic_t g_exit_signaled;

constexpr mode_t FileCreateMode =
    S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH;

constexpr mode_t DirCreateMode = FileCreateMode | S_IXUSR | S_IXGRP | S_IXOTH;

constexpr uint8_t DefaultZStdCompressionLevel = 3;
constexpr uint8_t DefaultVBufSegmentShift = 26;

constexpr uint64_t NotReadyCheckMask = (1UL << 25) - 1;

struct BlockCapOptions
{
    std::string exec_ring_path;
    std::optional<unsigned> connect_timeout;
    std::optional<uint8_t> event_zstd_level;
    std::optional<uint8_t> seqno_index_zstd_level;
    std::optional<uint8_t> vbuf_segment_shift;
    std::optional<uint64_t> seek_finalized_block;
    std::optional<uint64_t> seek_seqno;
    bool force_live;
};

void capture_blocks(
    BlockCapOptions const *, monad_bcap_archive *, uint64_t *last_finalized);

enum class LogPriority : uint8_t
{
    Emergency = LOG_EMERG,
    Alert = LOG_ALERT,
    Critical = LOG_CRIT,
    Error = LOG_ERR,
    Warning = LOG_WARNING,
    Notice = LOG_NOTICE,
    Info = LOG_INFO,
    Debug = LOG_DEBUG,
};

struct LogMessage
{
    LogPriority priority;
    std::optional<std::source_location> source_location;
    std::string message;
};

extern std::function<void(LogMessage const &)> g_log_writter;

template <typename... Args>
void write_log(
    LogPriority priority, std::optional<std::source_location> source_location,
    std::format_string<Args...> fmt, Args &&...args)
{
    g_log_writter(LogMessage{
        .priority = priority,
        .source_location = std::move(source_location),
        .message = std::format(fmt, std::forward<Args>(args)...)});
}

#define BCD_ERR(...)                                                           \
    write_log(LogPriority::Error, std::source_location::current(), __VA_ARGS__)

#define BCD_WARN(...)                                                          \
    write_log(                                                                 \
        LogPriority::Warning, std::source_location::current(), __VA_ARGS__)

#define BCD_INFO(...)                                                          \
    write_log(LogPriority::Info, std::source_location::current(), __VA_ARGS__)

#define BCD_INFO_NS(...) write_log(LogPriority::Info, std::nullopt, __VA_ARGS__)
