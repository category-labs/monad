#pragma once

#include <category/core/config.hpp>
#include <category/statesync/statesync_messages.h>

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

MONAD_NAMESPACE_END
