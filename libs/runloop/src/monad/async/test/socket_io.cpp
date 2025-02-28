#include <gtest/gtest.h>

#include "../../test_common.hpp"

#include "monad/async/socket_io.h"

#include <atomic>

#include <netinet/in.h>

TEST(socket_io, unregistered_buffers)
{
    struct shared_state_t
    {
        uint16_t localhost_port{0};

        monad_c_result server(monad_async_task task)
        {
            try {
                // Open a listening socket
                auto sock = make_socket(
                    task, AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0, 0);

                struct sockaddr_in localhost
                {
                    .sin_family = AF_INET, .sin_port = 0 /* any */,
                    .sin_addr = {.s_addr = htonl(INADDR_LOOPBACK)}, .sin_zero
                    {
                    }
                };

                to_result(
                    monad_async_task_socket_bind(
                        sock.get(), (sockaddr *)&localhost, sizeof(localhost)))
                    .value();
                to_result(monad_async_task_socket_listen(sock.get(), 0))
                    .value();
                localhost_port =
                    ntohs(((struct sockaddr_in *)&sock->addr)->sin_port);
                std::cout << "   Server socket listens on port "
                          << localhost_port << std::endl;
                to_result(
                    monad_async_task_socket_transfer_to_uring(task, sock.get()))
                    .value();

                std::cout << "   Server initiates accepting new connections."
                          << std::endl;
                // Accept new connections, suspending until a new one appears
                socket_ptr conn([&] {
                    monad_async_socket conn;
                    to_result(monad_async_task_socket_accept(
                                  &conn, task, sock.get(), 0))
                        .value();
                    return socket_ptr(
                        conn,
                        socket_deleter{task->current_executor.load(
                            std::memory_order_acquire)});
                }());
                // Close the listening socket
                sock.reset();
                auto *peer = (struct sockaddr_in *)&conn->addr;
                std::cout << "   Server accepts new connection from 0x"
                          << std::hex << peer->sin_addr.s_addr << std::dec
                          << ":" << peer->sin_port << std::endl;

                std::cout << "   Server initiates write to socket."
                          << std::endl;
                // Write "hello world" to the connecting socket
                monad_async_io_status status{};
                struct iovec iov[] = {{(void *)"hello world", 11}};
                struct msghdr msg = {};
                msg.msg_iov = iov;
                msg.msg_iovlen = 1;
                monad_async_task_socket_send(
                    &status, task, conn.get(), 0, &msg, 0);
                monad_async_io_status *completed;
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                auto byteswritten = to_result(status.result).value();
                std::cout << "   Server writes " << byteswritten
                          << " bytes to socket." << std::endl;

                std::cout << "   Server initiates shutdown of socket."
                          << std::endl;
                // Ensure written data gets flushed out.
                monad_async_task_socket_shutdown(
                    &status, task, conn.get(), SHUT_RDWR);
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                auto r = to_result(status.result);
                if (!r) {
                    if (r.assume_error() != errc::not_connected) {
                        r.value();
                    }
                }
                std::cout << "   Server has shutdown socket." << std::endl;
                return monad_c_make_success(0);
            }
            catch (std::exception const &e) {
                std::cerr << "FATAL: " << e.what() << std::endl;
                std::terminate();
            }
        }

        monad_c_result client(monad_async_task task)
        {
            try {
                // Connect to the listening socket
                auto sock = make_socket(
                    task, AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0, 0);
                to_result(
                    monad_async_task_socket_transfer_to_uring(task, sock.get()))
                    .value();

                monad_async_io_status status{};

                struct sockaddr_in addr
                {
                    .sin_family = AF_INET, .sin_port = htons(localhost_port),
                    .sin_addr = {.s_addr = htonl(INADDR_LOOPBACK)}, .sin_zero
                    {
                    }
                };

                std::cout << "   Client connects to port " << localhost_port
                          << "." << std::endl;
                monad_async_task_socket_connect(
                    &status, task, sock.get(), (sockaddr *)&addr, sizeof(addr));
                monad_async_io_status *completed;
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                std::cout << "   Client has connected." << std::endl;

                // Read from the socket
                std::cout << "   Client initiates read of socket." << std::endl;
                char buffer[256]{};
                struct iovec iov[] = {{(void *)buffer, 256}};
                struct msghdr msg = {};
                msg.msg_iov = iov;
                msg.msg_iovlen = 1;
                monad_async_task_socket_receivev(
                    &status, task, sock.get(), &msg, 0);
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                auto bytesread = to_result(status.result).value();

                std::cout << "   Client reads " << bytesread
                          << " bytes which are '" << (char *)iov[0].iov_base
                          << "'." << std::endl;
                EXPECT_EQ(bytesread, 11);
                EXPECT_STREQ((char *)iov[0].iov_base, "hello world");

                std::cout << "   Client initiates shutdown of socket."
                          << std::endl;
                // Gracefully close the socket
                monad_async_task_socket_shutdown(
                    &status, task, sock.get(), SHUT_RDWR);
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                auto r = to_result(status.result);
                if (!r) {
                    if (r.assume_error() != errc::not_connected) {
                        r.value();
                    }
                }
                std::cout << "   Client has shutdown socket." << std::endl;
                return monad_c_make_success(0);
            }
            catch (std::exception const &e) {
                std::cerr << "FATAL: " << e.what() << std::endl;
                std::terminate();
            }
        }
    }

    shared_state;

    // Make an executor
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 64;
    auto ex = make_executor(ex_attr);

    // Make a context switcher and two tasks, and attach the tasks to the
    // executor
    auto s = make_context_switcher(monad_context_switcher_sjlj);
    monad_async_task_attr t_attr{};
    auto t_server = make_task(s.get(), t_attr);
    t_server->derived.user_ptr = (void *)&shared_state;
    t_server->derived.user_code =
        +[](monad_context_task task) -> monad_c_result {
        return ((shared_state_t *)task->user_ptr)
            ->server((monad_async_task)task);
    };
    to_result(monad_async_task_attach(ex.get(), t_server.get(), nullptr))
        .value();
    auto t_client = make_task(s.get(), t_attr);
    t_client->derived.user_ptr = (void *)&shared_state;
    t_client->derived.user_code =
        +[](monad_context_task task) -> monad_c_result {
        return ((shared_state_t *)task->user_ptr)
            ->client((monad_async_task)task);
    };
    to_result(monad_async_task_attach(ex.get(), t_client.get(), nullptr))
        .value();

    // Run the executor until all tasks exit
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
}

TEST(socket_io, registered_buffers)
{
    struct shared_state_t
    {
        uint16_t localhost_port{0};

        monad_c_result server(monad_async_task task)
        {
            try {
                // Open a listening socket
                auto sock = make_socket(
                    task, AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0, 0);

                struct sockaddr_in localhost
                {
                    .sin_family = AF_INET, .sin_port = 0 /* any */,
                    .sin_addr = {.s_addr = htonl(INADDR_LOOPBACK)}, .sin_zero
                    {
                    }
                };

                to_result(
                    monad_async_task_socket_bind(
                        sock.get(), (sockaddr *)&localhost, sizeof(localhost)))
                    .value();
                to_result(monad_async_task_socket_listen(sock.get(), 0))
                    .value();
                localhost_port =
                    ntohs(((struct sockaddr_in *)&sock->addr)->sin_port);
                std::cout << "   Server socket listens on port "
                          << localhost_port << std::endl;
                to_result(
                    monad_async_task_socket_transfer_to_uring(task, sock.get()))
                    .value();

                std::cout << "   Server initiates accepting new connections."
                          << std::endl;
                // Accept new connections, suspending until a new one appears
                socket_ptr conn([&] {
                    monad_async_socket conn;
                    to_result(monad_async_task_socket_accept(
                                  &conn, task, sock.get(), 0))
                        .value();
                    return socket_ptr(
                        conn,
                        socket_deleter{task->current_executor.load(
                            std::memory_order_acquire)});
                }());
                // Close the listening socket
                sock.reset();
                auto *peer = (struct sockaddr_in *)&conn->addr;
                std::cout << "   Server accepts new connection from 0x"
                          << std::hex << peer->sin_addr.s_addr << std::dec
                          << ":" << peer->sin_port << std::endl;

                std::cout << "   Server initiates write to socket."
                          << std::endl;
                // Write "hello world" to the connecting socket
                // Get my registered buffer
                monad_async_task_registered_io_buffer buffer;
                to_result(
                    monad_async_task_claim_registered_socket_io_write_buffer(
                        &buffer, task, 11, {}))
                    .value();
                std::cout << "   Server has claimed registered i/o buffer no "
                          << buffer.index << " @ " << buffer.iov->iov_base
                          << " " << buffer.iov->iov_len << std::endl;
                memcpy(buffer.iov[0].iov_base, "hello world", 11);
                monad_async_io_status status{};
                struct iovec iov[] = {{buffer.iov[0].iov_base, 11}};
                struct msghdr msg = {};
                msg.msg_iov = iov;
                msg.msg_iovlen = 1;
                monad_async_task_socket_send(
                    &status, task, conn.get(), buffer.index, &msg, 0);
                monad_async_io_status *completed;
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                auto byteswritten = to_result(status.result).value();
                to_result(monad_async_task_release_registered_io_buffer(
                              task, buffer.index))
                    .value();
                std::cout
                    << "   Server releases registered i/o buffer after writing "
                    << byteswritten << " bytes to socket." << std::endl;

                std::cout << "   Server initiates shutdown of socket."
                          << std::endl;
                // Ensure written data gets flushed out.
                monad_async_task_socket_shutdown(
                    &status, task, conn.get(), SHUT_RDWR);
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                auto r = to_result(status.result);
                if (!r) {
                    if (r.assume_error() != errc::not_connected) {
                        r.value();
                    }
                }
                std::cout << "   Server has shutdown socket." << std::endl;
                return monad_c_make_success(0);
            }
            catch (std::exception const &e) {
                std::cerr << "FATAL: " << e.what() << std::endl;
                std::terminate();
            }
        }

        monad_c_result client(monad_async_task task)
        {
            try {
                // Connect to the listening socket
                auto sock = make_socket(
                    task, AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0, 0);
                to_result(
                    monad_async_task_socket_transfer_to_uring(task, sock.get()))
                    .value();

                monad_async_io_status status{};

                struct sockaddr_in addr
                {
                    .sin_family = AF_INET, .sin_port = htons(localhost_port),
                    .sin_addr = {.s_addr = htonl(INADDR_LOOPBACK)}, .sin_zero
                    {
                    }
                };

                std::cout << "   Client connects to port " << localhost_port
                          << "." << std::endl;
                monad_async_task_socket_connect(
                    &status, task, sock.get(), (sockaddr *)&addr, sizeof(addr));
                monad_async_io_status *completed;
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                std::cout << "   Client has connected." << std::endl;

                // Read from the socket
                std::cout << "   Client initiates read of socket." << std::endl;

                // Get my registered buffer
                struct monad_async_task_registered_io_buffer buffer
                {
                };

                monad_async_task_socket_receive(
                    &status, task, sock.get(), &buffer, 4096, 0);
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                auto bytesread = to_result(status.result).value();

                std::cout << "   Client releases registered i/o buffer index "
                          << buffer.index << " addr " << buffer.iov[0].iov_base
                          << " len " << buffer.iov[0].iov_len
                          << " after reading " << bytesread
                          << " bytes which are '"
                          << (char *)buffer.iov[0].iov_base << "'."
                          << std::endl;
                EXPECT_EQ(bytesread, 11);
                EXPECT_STREQ((char *)buffer.iov[0].iov_base, "hello world");
                to_result(monad_async_task_release_registered_io_buffer(
                              task, buffer.index))
                    .value();

                std::cout << "   Client initiates shutdown of socket."
                          << std::endl;
                // Gracefully close the socket
                monad_async_task_socket_shutdown(
                    &status, task, sock.get(), SHUT_RDWR);
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                auto r = to_result(status.result);
                if (!r) {
                    if (r.assume_error() != errc::not_connected) {
                        r.value();
                    }
                }
                std::cout << "   Client has shutdown socket." << std::endl;
                return monad_c_make_success(0);
            }
            catch (std::exception const &e) {
                std::cerr << "FATAL: " << e.what() << std::endl;
                std::terminate();
            }
        }
    } shared_state;

    // Make an executor
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 64;
    ex_attr.io_uring_ring.registered_buffers.small_count = 2;
    ex_attr.io_uring_ring.registered_buffers.small_kernel_allocated_count = 1;
    // Socket i/o never uses io_uring_wr_ring
    auto ex = make_executor(ex_attr);

    // Make a context switcher and two tasks, and attach the tasks to the
    // executor
    auto s = make_context_switcher(monad_context_switcher_sjlj);
    monad_async_task_attr t_attr{};
    auto t_server = make_task(s.get(), t_attr);
    t_server->derived.user_ptr = (void *)&shared_state;
    t_server->derived.user_code =
        +[](monad_context_task task) -> monad_c_result {
        return ((shared_state_t *)task->user_ptr)
            ->server((monad_async_task)task);
    };
    to_result(monad_async_task_attach(ex.get(), t_server.get(), nullptr))
        .value();
    auto t_client = make_task(s.get(), t_attr);
    t_client->derived.user_ptr = (void *)&shared_state;
    t_client->derived.user_code =
        +[](monad_context_task task) -> monad_c_result {
        return ((shared_state_t *)task->user_ptr)
            ->client((monad_async_task)task);
    };
    to_result(monad_async_task_attach(ex.get(), t_client.get(), nullptr))
        .value();

    // Run the executor until all tasks exit
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
    EXPECT_EQ(ex->total_io_submitted, ex->total_io_completed);
}
