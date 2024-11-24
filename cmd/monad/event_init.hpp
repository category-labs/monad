#pragma once

#include <monad/config.hpp>
#include <monad/event/event.h>

#include <cstdint>
#include <filesystem>
#include <span>
#include <thread>

struct monad_event_server;
extern "C" void monad_event_server_destroy(monad_event_server *);

MONAD_NAMESPACE_BEGIN

// clang-format off

struct EventRingConfig {
    bool enabled;                  ///< This event ring is enabled
    uint8_t ring_shift;            ///< Descriptor capacity == 2^(ring_shift)
    uint8_t payload_buffer_shift;  ///< Buffer size == 2^(payload_buffer_shift)
};

// clang-format on

extern EventRingConfig const DefaultEventRingConfig[MONAD_EVENT_QUEUE_COUNT];

extern std::jthread init_event_system(
    std::span<EventRingConfig const, MONAD_EVENT_QUEUE_COUNT>,
    std::filesystem::path const &event_socket_path, monad_event_server **);

MONAD_NAMESPACE_END
