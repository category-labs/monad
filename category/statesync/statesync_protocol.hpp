// Copyright (C) 2025 Category Labs, Inc.
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

#pragma once

#include <category/core/config.hpp>
#include <category/statesync/statesync_messages.h>
#include <category/statesync/statesync_version.h>

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

struct StatesyncProtocolV1_2 : StatesyncProtocol
{
    explicit StatesyncProtocolV1_2(uint32_t const version)
        : version_{version}
    {
    }

    virtual void send_request(
        monad_statesync_client_context *, uint64_t prefix) const override;

    virtual bool handle_upsert(
        monad_statesync_client_context *, monad_sync_type,
        unsigned char const *, uint64_t) const override;

protected:
    virtual bool apply_upsert(
        monad_statesync_client_context *, monad_sync_type,
        unsigned char const *, uint64_t) const;

    // the version this client declared to the peer; a request advertises it so
    // the server knows which records the client can decode
    uint32_t const version_;
};

struct StatesyncProtocolV1_3 : StatesyncProtocolV1_2
{
    using StatesyncProtocolV1_2::StatesyncProtocolV1_2;

protected:
    virtual bool apply_upsert(
        monad_statesync_client_context *, monad_sync_type,
        unsigned char const *, uint64_t) const override;
};

MONAD_NAMESPACE_END
