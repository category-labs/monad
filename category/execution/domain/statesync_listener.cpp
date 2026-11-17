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

#include <category/execution/domain/statesync_listener.hpp>

#include <category/core/log.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/statesync.hpp>

#include <quill/std/FilesystemPath.h>

#include <algorithm>
#include <cerrno>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <optional>
#include <stdexcept>
#include <string>
#include <thread>
#include <utility>
#include <vector>

#include <arpa/inet.h>
#include <asm-generic/socket.h>
#include <netdb.h>
#include <netinet/in.h>
#include <poll.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>

MONAD_DOMAIN_ANONYMOUS_NAMESPACE_BEGIN

// How long a send or a receive may stall before the connection is given up.
constexpr timeval IO_TIMEOUT{.tv_sec = 30, .tv_usec = 0};
constexpr int ACCEPT_POLL_MS = 100;

struct SocketAddress
{
    sockaddr_storage storage{};
    socklen_t length{0};

    sockaddr const *get() const
    {
        return reinterpret_cast<sockaddr const *>(&storage);
    }
};

// Parses the numeric address `host`, with `port` if given.
std::optional<SocketAddress>
parse_address(std::string const &host, char const *const port)
{
    addrinfo hints{};
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_flags = AI_NUMERICHOST | AI_NUMERICSERV;
    addrinfo *info = nullptr;
    if (::getaddrinfo(host.c_str(), port, &hints, &info) != 0) {
        return std::nullopt;
    }
    SocketAddress address;
    std::memcpy(&address.storage, info->ai_addr, info->ai_addrlen);
    address.length = info->ai_addrlen;
    ::freeaddrinfo(info);
    return address;
}

// Parses `ip:port` or `[ipv6]:port`.
std::optional<SocketAddress> parse_endpoint(std::string const &endpoint)
{
    auto const colon = endpoint.rfind(':');
    if (colon == std::string::npos || colon == 0) {
        return std::nullopt;
    }
    std::string host = endpoint.substr(0, colon);
    if (host.front() == '[' && host.back() == ']') {
        host = host.substr(1, host.size() - 2);
    }
    return parse_address(host, endpoint.c_str() + colon + 1);
}

// The address of `address` without its port, as inet_ntop gives it.
std::string to_string(SocketAddress const &address)
{
    char text[INET6_ADDRSTRLEN]{};
    if (address.storage.ss_family == AF_INET) {
        auto const *const in =
            reinterpret_cast<sockaddr_in const *>(&address.storage);
        ::inet_ntop(AF_INET, &in->sin_addr, text, sizeof(text));
    }
    else {
        auto const *const in6 =
            reinterpret_cast<sockaddr_in6 const *>(&address.storage);
        ::inet_ntop(AF_INET6, &in6->sin6_addr, text, sizeof(text));
    }
    return text;
}

void set_io_timeout(int const fd)
{
    ::setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &IO_TIMEOUT, sizeof(IO_TIMEOUT));
    ::setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &IO_TIMEOUT, sizeof(IO_TIMEOUT));
}

MONAD_DOMAIN_ANONYMOUS_NAMESPACE_END

MONAD_DOMAIN_NAMESPACE_BEGIN

StatesyncListener::StatesyncListener(
    std::string const &address, std::vector<std::string> const &allowed,
    uint64_t const domain_chain_id, std::filesystem::path domain_db_path)
    : domain_chain_id_{domain_chain_id}
    , domain_db_path_{std::move(domain_db_path)}
{
    for (auto const &entry : allowed) {
        auto const parsed = parse_address(entry, nullptr);
        if (!parsed.has_value()) {
            throw std::runtime_error{
                "statesync: not a numeric address: " + entry};
        }
        allowed_.push_back(to_string(*parsed));
    }
    auto const local = parse_endpoint(address);
    if (!local.has_value()) {
        throw std::runtime_error{
            "statesync: not a numeric ip:port: " + address};
    }
    fd_ = ::socket(local->storage.ss_family, SOCK_STREAM | SOCK_CLOEXEC, 0);
    int const reuse = 1;
    SocketAddress bound;
    bound.length = sizeof(bound.storage);
    if (fd_ == -1 ||
        ::setsockopt(fd_, SOL_SOCKET, SO_REUSEADDR, &reuse, sizeof(reuse)) !=
            0 ||
        ::bind(fd_, local->get(), local->length) != 0 ||
        ::listen(fd_, 4) != 0 ||
        ::getsockname(
            fd_, reinterpret_cast<sockaddr *>(&bound.storage), &bound.length) !=
            0) {
        std::string const reason = std::strerror(errno);
        if (fd_ != -1) {
            ::close(fd_);
        }
        throw std::runtime_error{
            "statesync: cannot listen on " + address + ": " + reason};
    }
    // The port is at the same offset in sockaddr_in and sockaddr_in6.
    port_ =
        ntohs(reinterpret_cast<sockaddr_in const *>(&bound.storage)->sin_port);
    thread_ = std::thread{[this] { run(); }};
}

StatesyncListener::~StatesyncListener()
{
    stop_ = true;
    thread_.join();
    ::close(fd_);
}

void StatesyncListener::run()
{
    while (!stop_) {
        pollfd waiting{.fd = fd_, .events = POLLIN, .revents = 0};
        if (::poll(&waiting, 1, ACCEPT_POLL_MS) <= 0) {
            continue;
        }
        SocketAddress peer;
        peer.length = sizeof(peer.storage);
        int const fd = ::accept4(
            fd_,
            reinterpret_cast<sockaddr *>(&peer.storage),
            &peer.length,
            SOCK_CLOEXEC);
        if (fd == -1) {
            continue;
        }
        auto const from = to_string(peer);
        if (std::ranges::find(allowed_, from) == allowed_.end()) {
            LOG_WARNING(
                "statesync: closed a connection from {}, which is not allowed",
                from);
        }
        else if (!std::filesystem::exists(domain_db_path_)) {
            LOG_WARNING(
                "statesync: {} asked for private domain {} before it has a "
                "state",
                from,
                domain_chain_id_);
        }
        else {
            set_io_timeout(fd);
            auto const served =
                serve_domain_state(fd, domain_chain_id_, domain_db_path_);
            if (served.has_error()) {
                LOG_WARNING(
                    "statesync: could not serve private domain {} to {}: {}",
                    domain_chain_id_,
                    from,
                    served.assume_error().message().c_str());
            }
            else {
                LOG_INFO(
                    "statesync: served private domain {} to {}",
                    domain_chain_id_,
                    from);
            }
        }
        ::close(fd);
    }
}

Result<int> connect_statesync_peer(std::string const &address)
{
    auto const peer = parse_endpoint(address);
    if (!peer.has_value()) {
        return StatesyncError::Connection;
    }
    int const fd =
        ::socket(peer->storage.ss_family, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if (fd == -1) {
        return StatesyncError::Connection;
    }
    set_io_timeout(fd);
    if (::connect(fd, peer->get(), peer->length) != 0) {
        ::close(fd);
        return StatesyncError::Connection;
    }
    return fd;
}

MONAD_DOMAIN_NAMESPACE_END
