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

#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/basic_formatter.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/statesync/statesync_server_network.hpp>
#include <category/statesync/statesync_thread.hpp>

#include <gtest/gtest.h>

#include <boost/scope_exit.hpp>

#include <array>
#include <chrono>
#include <fcntl.h>
#include <filesystem>
#include <optional>
#include <poll.h>
#include <sys/eventfd.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <thread>
#include <unistd.h>

namespace
{
    // Returns a socket path unique per process to avoid bind() collisions when
    // tests run in parallel. Assumes TMPDIR is short enough that the full path
    // stays within sun_path (108 bytes).
    std::filesystem::path unique_socket_path(std::string_view const name)
    {
        return std::filesystem::temp_directory_path() /
               (std::string(name) + "_" + std::to_string(::getpid()) + ".sock");
    }

    // RAII wrapper for a temporary DB file with no persistent directory entry
    // (accessed via /proc/self/fd/<n>, auto-deleted when fd is closed).
    // The constructor also initializes the on-disk DB format so the file is
    // ready for subsequent Db opens.
    struct TempDb
    {
        int fd;
        std::string path;

        TempDb()
            : fd{MONAD_ASYNC_NAMESPACE::make_temporary_inode()}
            , path{"/proc/self/fd/" + std::to_string(fd)}
        {
            MONAD_ASSERT(fd != -1);
            MONAD_ASSERT(
                -1 !=
                ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
            monad::OnDiskMachine machine;
            // Initialize the on-disk DB format; the Db object is not needed
            // after this point.
            (void)monad::mpt::Db{
                machine,
                monad::mpt::OnDiskDbConfig{
                    .append = false, .dbname_paths = {path}}};
        }

        TempDb(TempDb const &) = delete;
        TempDb &operator=(TempDb const &) = delete;

        ~TempDb()
        {
            ::close(fd);
        }
    };
}

TEST(StateSyncThread, shutdown_via_jthread_stop_token)
{
    // Tests production shutdown: request_stop() → stop_callback →
    // signal_shutdown() → eventfd → poll() wakes → thread exits

    std::filesystem::path const socket_path =
        unique_socket_path("test_statesync_prod");
    std::filesystem::remove(socket_path);
    BOOST_SCOPE_EXIT(&socket_path)
    {
        std::filesystem::remove(socket_path);
    }
    BOOST_SCOPE_EXIT_END

    int const listen_fd = socket(AF_UNIX, SOCK_STREAM, 0);
    ASSERT_GE(listen_fd, 0) << "Failed to create socket: " << strerror(errno);
    BOOST_SCOPE_EXIT(&listen_fd)
    {
        close(listen_fd);
    }
    BOOST_SCOPE_EXIT_END

    struct sockaddr_un addr;
    memset(&addr, 0, sizeof(addr));
    addr.sun_family = AF_UNIX;
    strncpy(addr.sun_path, socket_path.c_str(), sizeof(addr.sun_path) - 1);

    ASSERT_EQ(bind(listen_fd, (struct sockaddr *)&addr, sizeof(addr)), 0)
        << "Failed to bind socket: " << strerror(errno);
    ASSERT_EQ(listen(listen_fd, 1), 0)
        << "Failed to listen on socket: " << strerror(errno);

    TempDb const db_file;

    monad::mpt::AsyncIOContext io_ctx{
        monad::mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {db_file.path}}};
    monad::mpt::Db db{io_ctx};
    monad::TrieDb triedb(db);

    std::optional<monad_statesync_server_network> net;
    std::thread connect_thread([&]() { net.emplace(socket_path.c_str()); });

    int const client_fd = accept(listen_fd, nullptr, nullptr);
    ASSERT_GE(client_fd, 0)
        << "Failed to accept connection: " << strerror(errno);
    BOOST_SCOPE_EXIT(&client_fd)
    {
        if (client_fd >= 0) {
            close(client_fd);
        }
    }
    BOOST_SCOPE_EXIT_END

    connect_thread.join();

    std::unique_ptr<monad::StateSyncServer> sync_server =
        monad::make_statesync_server(monad::StateSyncServerConfig{
            .triedb = &triedb,
            .network = &*net,
            .ro_sq_thread_cpu = std::nullopt,
            .dbname_paths = {db_file.path}});

    std::this_thread::sleep_for(std::chrono::milliseconds(50));

    sync_server->thread.request_stop();
    sync_server->thread.join();
}

TEST(StateSyncThread, shutdown_during_reconnect)
{
    // Tests shutdown works when connect() is stuck in retry loop

    std::filesystem::path const socket_path =
        unique_socket_path("test_statesync_reconnect");
    std::filesystem::remove(socket_path);
    BOOST_SCOPE_EXIT(&socket_path)
    {
        std::filesystem::remove(socket_path);
    }
    BOOST_SCOPE_EXIT_END

    int const listen_fd = socket(AF_UNIX, SOCK_STREAM, 0);
    ASSERT_GE(listen_fd, 0) << "Failed to create socket: " << strerror(errno);
    BOOST_SCOPE_EXIT(&listen_fd)
    {
        close(listen_fd);
    }
    BOOST_SCOPE_EXIT_END

    struct sockaddr_un addr;
    memset(&addr, 0, sizeof(addr));
    addr.sun_family = AF_UNIX;
    strncpy(addr.sun_path, socket_path.c_str(), sizeof(addr.sun_path) - 1);

    ASSERT_EQ(bind(listen_fd, (struct sockaddr *)&addr, sizeof(addr)), 0)
        << "Failed to bind socket: " << strerror(errno);
    ASSERT_EQ(listen(listen_fd, 1), 0)
        << "Failed to listen on socket: " << strerror(errno);

    TempDb const db_file;

    monad::mpt::AsyncIOContext io_ctx{
        monad::mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {db_file.path}}};
    monad::mpt::Db db{io_ctx};
    monad::TrieDb triedb(db);

    std::optional<monad_statesync_server_network> net;
    std::thread connect_thread([&]() { net.emplace(socket_path.c_str()); });

    int client_fd = accept(listen_fd, nullptr, nullptr);
    ASSERT_GE(client_fd, 0)
        << "Failed to accept connection: " << strerror(errno);
    BOOST_SCOPE_EXIT(&client_fd)
    {
        if (client_fd >= 0) {
            close(client_fd);
        }
    }
    BOOST_SCOPE_EXIT_END

    connect_thread.join();

    std::unique_ptr<monad::StateSyncServer> sync_server =
        monad::make_statesync_server(monad::StateSyncServerConfig{
            .triedb = &triedb,
            .network = &*net,
            .ro_sq_thread_cpu = std::nullopt,
            .dbname_paths = {db_file.path}});

    std::this_thread::sleep_for(std::chrono::milliseconds(50));

    close(client_fd);
    client_fd = -1;
    std::this_thread::sleep_for(std::chrono::milliseconds(100));

    sync_server->thread.request_stop();
    sync_server->thread.join();
}
