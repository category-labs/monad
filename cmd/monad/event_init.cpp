#include <monad/event/event.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_server.h>

#include <csignal>
#include <cstdint>
#include <filesystem>
#include <span>
#include <thread>

#include <pthread.h>
#include <time.h>

#include <quill/LogLevel.h>
#include <quill/Quill.h>

#include "event_init.hpp"

namespace fs = std::filesystem;

extern sig_atomic_t volatile stop;

/*
 * Event server functions
 */

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

std::jthread monad::init_event_system(
    std::span<EventRingConfig const, MONAD_EVENT_QUEUE_COUNT> ring_configs,
    fs::path const &event_socket_path, monad_event_server **event_server)
{
    for (uint8_t i = 0; EventRingConfig const &c : ring_configs) {
        monad_event_recorder_set_enabled(
            static_cast<monad_event_queue_type>(i), c.enabled);
    }

    // Host an event server on a separate thread, so external clients can
    // connect
    return init_event_server(event_socket_path, event_server);
}
