#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/statesync/statesync_messages.h>

#include <quill/Quill.h>

#include <chrono>
#include <sys/socket.h>
#include <sys/un.h>
#include <thread>

struct monad_statesync_server_network
{
    int fd;
    monad::byte_string obuf;

    monad_statesync_server_network(char const *const path)
        : fd{socket(AF_UNIX, SOCK_STREAM, 0)}
    {
        struct sockaddr_un addr;
        memset(&addr, 0, sizeof(addr));
        addr.sun_family = AF_UNIX;
        strncpy(addr.sun_path, path, sizeof(addr.sun_path) - 1);
        while (connect(fd, (sockaddr *)&addr, sizeof(addr)) != 0) {
            std::this_thread::sleep_for(std::chrono::milliseconds(1));
        }
    }
};

MONAD_NAMESPACE_BEGIN

namespace
{
    void send(int const fd, byte_string_view const buf)
    {
        size_t nsent = 0;
        while (nsent < buf.size()) {
            ssize_t const res =
                ::send(fd, buf.data() + nsent, buf.size() - nsent, 0);
            if (res == -1) {
                continue;
            }
            nsent += static_cast<size_t>(res);
        }
    }
}

ssize_t statesync_server_recv(
    monad_statesync_server_network *const net, unsigned char *buf, size_t n)
{
    return recv(net->fd, buf, n, MSG_DONTWAIT);
}

void statesync_server_send_upsert(
    monad_statesync_server_network *const net, unsigned char const *const key,
    uint64_t const key_size, unsigned char const *const value,
    uint64_t const value_size, bool const code)
{
    auto const start = std::chrono::steady_clock::now();
    net->obuf.push_back(SyncTypeUpsertHeader);
    monad_sync_upsert_header const hdr{
        .code = code, .key_size = key_size, .value_size = value_size};
    net->obuf.append(
        reinterpret_cast<unsigned char const *>(&hdr), sizeof(hdr));
    net->obuf.append(key, key_size);
    net->obuf.append(value, value_size);

    if (net->obuf.size() >= (1 << 30)) {
        send(net->fd, net->obuf);
        net->obuf.clear();
    }

    LOG_INFO(
        "sent upsert {} code={} ns={}",
        fmt::format(
            "key=0x{:02x} value=0x{:02x}",
            fmt::join(std::as_bytes(std::span(key, key_size)), ""),
            fmt::join(std::as_bytes(std::span(value, value_size)), "")),
        code,
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            std::chrono::steady_clock::now() - start));
}

void statesync_server_send_done(
    monad_statesync_server_network *const net, monad_sync_done const msg)
{
    auto const start = std::chrono::steady_clock::now();
    net->obuf.push_back(SyncTypeDone);
    net->obuf.append(
        reinterpret_cast<unsigned char const *>(&msg), sizeof(msg));
    send(net->fd, net->obuf);
    net->obuf.clear();
    LOG_INFO(
        "sent done success={} prefix={} n={} time={}",
        msg.success,
        msg.prefix,
        msg.n,
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - start));
}

MONAD_NAMESPACE_END
