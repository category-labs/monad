#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/statesync/statesync_messages.h>

#include <quill/Quill.h>

#include <chrono>
#include <queue>
#include <sys/eventfd.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <thread>
#include <utility>

struct monad_statesync_server_network
{
    int fd;
    int stop_fd;
    monad::byte_string obuf;
    std::thread read_thread;
    std::condition_variable cv;
    std::mutex mtx;
    std::queue<monad_sync_request> rqs;
    std::atomic_bool *aborted = nullptr;

    static void thread_func(monad_statesync_server_network *const net)
    {
        enum class State
        {
            READ_TYPE,
            READ_REQ,
        };

        unsigned char buf[sizeof(monad_sync_request)];
        size_t off = 0;
        auto state = State::READ_TYPE;

        pthread_setname_np(pthread_self(), "statesync read request thread");

        while (true) {
            fd_set read_fds;
            FD_ZERO(&read_fds);
            FD_SET(net->fd, &read_fds);
            FD_SET(net->stop_fd, &read_fds);

            int max_fd = std::max(net->fd, net->stop_fd);
            int ret = select(max_fd + 1, &read_fds, nullptr, nullptr, nullptr);

            if (ret == -1 && errno != EINTR) {
                perror("select");
                MONAD_ASSERT(false);
            }

            if (FD_ISSET(net->stop_fd, &read_fds)) {
                // stop_fd is signaled, exit the loop
                break;
            }

            if (!FD_ISSET(net->fd, &read_fds)) {
                continue;
            }

            if (state == State::READ_TYPE) {
                auto read_ret = read(net->fd, buf, 1);
                if (read_ret == 0) {
                    continue;
                }
                MONAD_ASSERT(read_ret == 1);
                unsigned char const type = buf[0];
                if (type == SYNC_TYPE_REQUEST) {
                    state = State::READ_REQ;
                    // Reset aborted when new request is received
                    if (net->aborted != nullptr) {
                        *net->aborted = false;
                    }
                }
                else if (type == SYNC_TYPE_ABORT) {
                    if (net->aborted != nullptr) {
                        *net->aborted = true;
                    }
                }
                else {
                    MONAD_ASSERT(false);
                }
            }
            else {
                auto read_ret =
                    read(net->fd, buf + off, sizeof(monad_sync_request) - off);
                if (read_ret == 0) {
                    continue;
                }
                MONAD_ASSERT(
                    read_ret > 0 && static_cast<size_t>(read_ret) <=
                                        sizeof(monad_sync_request) - off);
                off += static_cast<size_t>(read_ret);
                if (off == sizeof(monad_sync_request)) {
                    auto const &rq =
                        monad::unaligned_load<monad_sync_request>(buf);
                    {
                        std::lock_guard<std::mutex> lock(net->mtx);
                        net->rqs.push(rq);
                    }
                    net->cv.notify_one();
                    off = 0;
                    state = State::READ_TYPE;
                }
            }
        }
    }

    monad_statesync_server_network(char const *const path)
        : fd{socket(AF_UNIX, SOCK_STREAM, 0)}
        , stop_fd{eventfd(0, 0)}
    {
        MONAD_ASSERT(stop_fd != -1);
        MONAD_ASSERT(fd != -1);

        struct sockaddr_un addr;
        memset(&addr, 0, sizeof(addr));
        addr.sun_family = AF_UNIX;
        strncpy(addr.sun_path, path, sizeof(addr.sun_path) - 1);
        while (connect(fd, (sockaddr *)&addr, sizeof(addr)) != 0) {
            std::this_thread::sleep_for(std::chrono::milliseconds(1));
        }

        read_thread = std::thread(thread_func, this);
    }

    ~monad_statesync_server_network()
    {
        auto ret = eventfd_write(stop_fd, 1);
        MONAD_ASSERT(ret == 0);
        read_thread.join();
        (void)close(stop_fd);
        (void)close(fd);
    }
};

MONAD_NAMESPACE_BEGIN

namespace
{
    constexpr size_t SEND_BATCH_SIZE = 64 * 1024;

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

monad_sync_request
statesync_server_recv(monad_statesync_server_network *const net)
{
    std::unique_lock<std::mutex> lock(net->mtx);
    net->cv.wait(lock, [&] { return !net->rqs.empty(); });
    monad_sync_request rq = net->rqs.front();
    net->rqs.pop();
    return rq;
}

void statesync_server_send_upsert(
    monad_statesync_server_network *const net, monad_sync_type const type,
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
        send(net->fd, net->obuf);
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
}

void statesync_server_send_done(
    monad_statesync_server_network *const net, monad_sync_done const msg)
{
    [[maybe_unused]] auto const start = std::chrono::steady_clock::now();
    net->obuf.push_back(SYNC_TYPE_DONE);
    net->obuf.append(
        reinterpret_cast<unsigned char const *>(&msg), sizeof(msg));
    send(net->fd, net->obuf);
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
