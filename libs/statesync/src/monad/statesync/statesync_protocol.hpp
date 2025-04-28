#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/statesync/statesync_messages.h>

struct monad_statesync_client_context;

MONAD_NAMESPACE_BEGIN

struct StatesyncProtocol
{
    virtual ~StatesyncProtocol() = default;

    virtual void
    send_request(monad_statesync_client_context *, uint64_t prefix) const = 0;

    virtual bool handle_upsert(
        monad_statesync_client_context *, monad_sync_type,
        unsigned char const *, uint64_t) const = 0;
};

struct StatesyncProtocolV1 : StatesyncProtocol
{
    virtual void send_request(
        monad_statesync_client_context *, uint64_t prefix) const override;

    virtual bool handle_upsert(
        monad_statesync_client_context *, monad_sync_type,
        unsigned char const *, uint64_t) const override;
};

inline byte_string from_prefix(uint64_t const prefix, size_t const n_bytes)
{
    byte_string bytes;
    for (size_t i = 0; i < n_bytes; ++i) {
        bytes.push_back((prefix >> ((n_bytes - i - 1) * 8)) & 0xff);
    }
    return bytes;
}

MONAD_NAMESPACE_END
