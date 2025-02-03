#include <atomic> // Must precede C headers or <stdatomic.h> causes problems

#include <monad/config.hpp>
#include <monad/event/event.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_server.h>

#include <charconv>
#include <concepts>
#include <csignal>
#include <cstdint>
#include <filesystem>
#include <format>
#include <ranges>
#include <span>
#include <system_error>
#include <thread>
#include <utility>

#include <pthread.h>
#include <time.h>

#include <quill/LogLevel.h>
#include <quill/Quill.h>

#include "event.hpp"

namespace fs = std::filesystem;

template <std::integral I>
static std::string try_parse_int_token(std::string_view s, I *i)
{
    std::from_chars_result const r = std::from_chars(begin(s), end(s), *i, 10);
    if (r.ptr != data(s) + size(s)) {
        return std::format("{} contains non-integer characters", s);
    }
    if (static_cast<int>(r.ec) != 0) {
        std::error_condition const e{r.ec};
        return std::format(
            "could not parse {} as integer: {} ({})",
            s,
            e.message(),
            e.value());
    }
    return {};
}

/*
 * Event server functions
 */

// Logging callback that writes to Quill
static void monad_event_server_logger(int severity, char const *msg, void *ctx)
{
    constexpr quill::LogLevel syslog_to_quill_levels[] = {
        quill::LogLevel::Critical,
        quill::LogLevel::Critical,
        quill::LogLevel::Critical,
        quill::LogLevel::Error,
        quill::LogLevel::Warning,
        quill::LogLevel::Info,
        quill::LogLevel::Info,
        quill::LogLevel::Debug};
    auto *const logger = static_cast<quill::Logger *>(ctx);
    if (!logger->should_log(syslog_to_quill_levels[severity])) {
        return;
    }
    QUILL_DYNAMIC_LOG(logger, syslog_to_quill_levels[severity], "{}", msg);
}

static void event_server_thread_main(
    std::stop_token const token, monad_event_server *server)
{
    extern sig_atomic_t volatile stop;
    pthread_setname_np(pthread_self(), "event_server");
    timespec const timeout{.tv_sec = 1, .tv_nsec = 30'000'000};
    while (!token.stop_requested() && stop == 0) {
        (void)monad_event_server_process_work(
            server, &timeout, nullptr, nullptr);
    }
}

static std::jthread init_event_server(
    fs::path const &event_socket_path, monad_event_server **event_server)
{
    int srv_rc;
    monad_event_server_options event_server_opts = {
        .log_fn = monad_event_server_logger,
        .log_context = quill::get_root_logger(),
        .socket_path = MONAD_EVENT_DEFAULT_SOCKET_PATH};
    // Note the comma operator because c_str() is only temporary
    event_server_opts.socket_path = event_socket_path.c_str(),
    srv_rc = monad_event_server_create(&event_server_opts, event_server);
    if (srv_rc != 0) {
        // TODO(ken): should this be an exception?
        LOG_ERROR("event server initialization error, server is disabled");
        return {};
    }

    // Launch the event server as a separate thread
    return std::jthread{event_server_thread_main, *event_server};
}

MONAD_NAMESPACE_BEGIN

std::variant<EventRingConfig, std::string>
try_parse_event_ring_config(std::string_view s)
{
    std::vector<std::string_view> tokens;
    EventRingConfig cfg;

    // TODO(ken): should be std::ranges::to
    for (auto t : std::views::split(s, ':')) {
        tokens.emplace_back(t);
    }

    if (size(tokens) < 2 || size(tokens) > 4) {
        return std::format(
            "input `{}` does not have "
            "expected format "
            "<name>:<enabled>[:<ring-shift>:<payload-buffer-shift>]",
            s);
    }
    if (tokens[0] == "exec") {
        cfg.ring_type = MONAD_EVENT_RING_EXEC;
    }
    else if (tokens[0] == "trace") {
        cfg.ring_type = MONAD_EVENT_RING_TRACE;
    }
    else {
        return std::format(
            "expected ring type 'exec' or 'trace', found {}", tokens[0]);
    }

    if (tokens[1] == "1" || tokens[1] == "true") {
        cfg.enabled = true;
    }
    else if (tokens[1] == "0" || tokens[1] == "false") {
        cfg.enabled = false;
    }
    else {
        return std::format("could not parse `{}` as <enabled>", tokens[1]);
    }

    if (size(tokens) < 3 || tokens[2].empty()) {
        cfg.ring_shift = DefaultEventRingConfig[cfg.ring_type].ring_shift;
    }
    else if (auto err = try_parse_int_token(tokens[2], &cfg.ring_shift);
             !empty(err)) {
        return std::format(
            "parse error in ring_shift `{}`: {}", tokens[2], err);
    }

    if (size(tokens) < 4 || tokens[3].empty()) {
        cfg.payload_buffer_shift =
            DefaultEventRingConfig[cfg.ring_type].payload_buffer_shift;
    }
    else if (auto err =
                 try_parse_int_token(tokens[3], &cfg.payload_buffer_shift);
             !empty(err)) {
        return std::format(
            "parse error in payload_buffer_shift `{}`: {}", tokens[3], err);
    }

    return cfg;
}

std::jthread init_event_system(
    std::span<EventRingConfig const> ring_configs,
    fs::path const &event_socket_path, monad_event_server **event_server)
{
    // Configure and enable event rings
    for (EventRingConfig const &c : ring_configs) {
        if (monad_event_recorder_configure(
                c.ring_type, c.ring_shift, c.payload_buffer_shift) != 0) {
            LOG_ERROR(
                "unable to configure event ring {}:\n{}",
                std::to_underlying(c.ring_type),
                monad_event_recorder_get_last_error());
        }
        monad_event_recorder_set_enabled(c.ring_type, c.enabled);
    }

    // Launch an event server on a new thread
    return init_event_server(event_socket_path, event_server);
}

EventRingConfig const DefaultEventRingConfig[] = {
    {.ring_type = MONAD_EVENT_RING_EXEC,
     .enabled = true,
     .ring_shift = MONAD_EVENT_DEFAULT_EXEC_RING_SHIFT,
     .payload_buffer_shift = MONAD_EVENT_DEFAULT_EXEC_PAYLOAD_BUF_SHIFT},
    {.ring_type = MONAD_EVENT_RING_TRACE,
     .enabled = false,
     .ring_shift = MONAD_EVENT_DEFAULT_EXEC_RING_SHIFT,
     .payload_buffer_shift = MONAD_EVENT_DEFAULT_EXEC_PAYLOAD_BUF_SHIFT}};

MONAD_NAMESPACE_END
