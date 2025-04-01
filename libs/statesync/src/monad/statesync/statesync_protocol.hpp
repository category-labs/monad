#pragma once

#include <monad/config.hpp>
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

// TODO: remove V1 support once all nodes are upgraded since V1 is only
// backwards compatible with V2 if both can support the same prefix size
// (whether represented in nibbles or bytes)
struct StatesyncProtocolV2 : StatesyncProtocolV1
{
    virtual void send_request(
        monad_statesync_client_context *, uint64_t prefix) const override;
};

MONAD_NAMESPACE_END
