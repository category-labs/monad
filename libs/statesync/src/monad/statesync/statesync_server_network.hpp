#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/statesync/statesync_messages.h>

#include <quill/Quill.h>

#include <chrono>
#include <sys/socket.h>
#include <sys/un.h>
#include <thread>
#include <utility>

struct monad_statesync_server_network
{
    int fd;
    monad::byte_string obuf;
    std::string path;

    monad_statesync_server_network(char const *const path)
        : fd{-1}
        , path(path)
    {
        ensure_connected();
    }

    void ensure_connected()
    {
        if (fd != -1) {
            return;
        }
        fd = socket(AF_UNIX, SOCK_STREAM, 0);
        MONAD_ASSERT(fd >= 0);
        struct sockaddr_un addr;
        memset(&addr, 0, sizeof(addr));
        addr.sun_family = AF_UNIX;
        strncpy(addr.sun_path, path.c_str(), sizeof(addr.sun_path) - 1);
        while (::connect(fd, (sockaddr *)&addr, sizeof(addr)) != 0) {
            std::this_thread::sleep_for(std::chrono::milliseconds(1));
        }
    }
};

MONAD_NAMESPACE_BEGIN

namespace
{
    constexpr size_t SEND_BATCH_SIZE = 64 * 1024;

    /// Returns true if send succeeded, otherwise false.
    bool send(monad_statesync_server_network *net, byte_string_view const buf)
    {
        size_t nsent = 0;
        if (net->fd == -1) {
            return false;
        }
        while (nsent < buf.size()) {
            ssize_t const res =
                ::send(net->fd, buf.data() + nsent, buf.size() - nsent, 0);
            if (res == -1) {
                if (errno == EINTR) {
                    continue;
                }
                else if (errno == EPIPE || errno == ECONNRESET) {
                    LOG_INFO("statesync connection closed, exiting traverse");
                    close(net->fd);
                    net->fd = -1;
                    return false;
                }
                else {
                    MONAD_ASSERT(false);
                }
            }
            nsent += static_cast<size_t>(res);
        }
        return true;
    }
}

ssize_t statesync_server_recv(
    monad_statesync_server_network *net, unsigned char *buf, size_t n)
{
    while (true) {
        net->ensure_connected();
        auto const res = recv(net->fd, buf, n, 0);
        if (res > 0) {
            return res;
        }
        else if (res == 0) {
            LOG_INFO("statesync connection closed, reconnecting");
            close(net->fd);
            net->fd = -1;
        }
        else {
            if (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK) {
                continue;
            }
            MONAD_ASSERT(false);
        }
    }
}

bool statesync_server_send_upsert(
    monad_statesync_server_network *net, monad_sync_type const type,
    unsigned char const *const v1, uint64_t const size1,
    unsigned char const *const v2, uint64_t const size2)
{
    MONAD_ASSERT(v1 != nullptr || size1 == 0);
    MONAD_ASSERT(v2 != nullptr || size2 == 0);
    MONAD_ASSERT(
        type == SYNC_TYPE_UPSERT_CODE || type == SYNC_TYPE_UPSERT_ACCOUNT ||
        type == SYNC_TYPE_UPSERT_STORAGE ||
        type == SYNC_TYPE_UPSERT_ACCOUNT_DELETE ||
        type == SYNC_TYPE_UPSERT_STORAGE_DELETE ||
        type == SYNC_TYPE_UPSERT_HEADER);

    [[maybe_unused]] auto const start = std::chrono::steady_clock::now();
    net->obuf.push_back(type);
    uint64_t const size = size1 + size2;
    net->obuf.append(
        reinterpret_cast<unsigned char const *>(&size), sizeof(size));
    if (v1 != nullptr) {
        net->obuf.append(v1, size1);
    }
    if (v2 != nullptr) {
        net->obuf.append(v2, size2);
    }

    if (net->obuf.size() >= SEND_BATCH_SIZE) {
        if (!send(net, net->obuf)) {
            return false;
        }
        net->obuf.clear();
    }

    LOG_DEBUG(
        "sending upsert type={} {} ns={}",
        std::to_underlying(type),
        fmt::format(
            "v1=0x{:02x} v2=0x{:02x}",
            fmt::join(std::as_bytes(std::span(v1, size1)), ""),
            fmt::join(std::as_bytes(std::span(v2, size2)), "")),
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            std::chrono::steady_clock::now() - start));
    return true;
}

void statesync_server_send_done(
    monad_statesync_server_network *net, monad_sync_done const msg)
{
    [[maybe_unused]] auto const start = std::chrono::steady_clock::now();
    net->obuf.push_back(SYNC_TYPE_DONE);
    net->obuf.append(
        reinterpret_cast<unsigned char const *>(&msg), sizeof(msg));
    (void)send(net, net->obuf);
    net->obuf.clear();
    LOG_DEBUG(
        "sending done success={} prefix={} n={} time={}",
        msg.success,
        msg.prefix,
        msg.n,
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - start));
}

MONAD_NAMESPACE_END
