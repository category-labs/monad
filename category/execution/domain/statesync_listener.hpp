// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <string>
#include <thread>
#include <vector>

MONAD_DOMAIN_NAMESPACE_BEGIN

// Serves a domain's state to the peers on an allowlist, one at a time, from a
// thread of its own. A connection from any other address is closed unanswered:
// the state of a private domain goes out in the clear, to whoever is at an
// allowed address.
class StatesyncListener
{
    uint64_t domain_chain_id_;
    std::filesystem::path domain_db_path_;
    // Allowed peer addresses, in the form inet_ntop gives them.
    std::vector<std::string> allowed_;
    int fd_{-1};
    uint16_t port_{0};
    std::atomic<bool> stop_{false};
    std::thread thread_;

    void run();

public:
    // Listens on `address`, an `ip:port` or `[ipv6]:port`, and serves the db at
    // `domain_db_path` once it exists. Throws std::runtime_error if `address`
    // or an entry of `allowed` is not a numeric address, or the socket cannot
    // be bound.
    StatesyncListener(
        std::string const &address, std::vector<std::string> const &allowed,
        uint64_t domain_chain_id, std::filesystem::path domain_db_path);
    ~StatesyncListener();

    StatesyncListener(StatesyncListener const &) = delete;
    StatesyncListener &operator=(StatesyncListener const &) = delete;

    // The port it listens on, which the system picks if `address` has port 0.
    uint16_t port() const
    {
        return port_;
    }
};

// Connects to the statesync peer at `address`, an `ip:port` or `[ipv6]:port`,
// and returns the socket, which the caller closes. Fails with
// StatesyncError::Connection.
Result<int> connect_statesync_peer(std::string const &address);

MONAD_DOMAIN_NAMESPACE_END
