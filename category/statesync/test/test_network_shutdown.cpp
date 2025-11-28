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

TEST(StateSyncThread, shutdown_via_jthread_stop_token)
{
    // Tests production shutdown: request_stop() → stop_callback →
    // signal_shutdown() → eventfd → poll() wakes → thread exits

    std::filesystem::path const socket_path =
        std::filesystem::temp_directory_path() / "test_statesync_prod.sock";
    std::filesystem::remove(socket_path);
    BOOST_SCOPE_EXIT(&socket_path)
    {
        std::filesystem::remove(socket_path);
    }
    BOOST_SCOPE_EXIT_END

    int const listen_fd = socket(AF_UNIX, SOCK_STREAM, 0);
    ASSERT_GE(listen_fd, 0) << "Failed to create socket: " << strerror(errno);

    struct sockaddr_un addr;
    memset(&addr, 0, sizeof(addr));
    addr.sun_family = AF_UNIX;
    strncpy(addr.sun_path, socket_path.c_str(), sizeof(addr.sun_path) - 1);

    ASSERT_EQ(bind(listen_fd, (struct sockaddr *)&addr, sizeof(addr)), 0)
        << "Failed to bind socket: " << strerror(errno);
    ASSERT_EQ(listen(listen_fd, 1), 0)
        << "Failed to listen on socket: " << strerror(errno);

    std::filesystem::path const dbname =
        std::filesystem::temp_directory_path() / "test_triedb_shutdown.mdb";
    std::filesystem::remove(dbname);
    BOOST_SCOPE_EXIT(&dbname)
    {
        std::filesystem::remove(dbname);
    }
    BOOST_SCOPE_EXIT_END

    int const fd =
        ::open(dbname.c_str(), O_RDWR | O_CREAT | O_TRUNC | O_CLOEXEC, 0644);
    ASSERT_GE(fd, 0) << "Failed to create db file: " << strerror(errno);
    ASSERT_EQ(::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)), 0)
        << "Failed to truncate db file: " << strerror(errno);
    ::close(fd);

    monad::mpt::AsyncIOContext io_ctx{
        monad::mpt::OnDiskDbConfig{.append = false, .dbname_paths = {dbname}}};
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
    close(listen_fd);

    std::unique_ptr<monad::StateSyncServer> sync_server =
        monad::make_statesync_server(monad::StateSyncServerConfig{
            .triedb = &triedb,
            .network = &*net,
            .ro_sq_thread_cpu = std::nullopt,
            .dbname_paths = {dbname}});

    std::this_thread::sleep_for(std::chrono::milliseconds(50));

    sync_server->thread.request_stop();
    sync_server->thread.join();
}

TEST(StateSyncThread, shutdown_during_reconnect)
{
    // Tests shutdown works when connect() is stuck in retry loop

    std::filesystem::path const socket_path =
        std::filesystem::temp_directory_path() /
        "test_statesync_reconnect.sock";
    std::filesystem::remove(socket_path);
    BOOST_SCOPE_EXIT(&socket_path)
    {
        std::filesystem::remove(socket_path);
    }
    BOOST_SCOPE_EXIT_END

    int const listen_fd = socket(AF_UNIX, SOCK_STREAM, 0);
    ASSERT_GE(listen_fd, 0) << "Failed to create socket: " << strerror(errno);

    struct sockaddr_un addr;
    memset(&addr, 0, sizeof(addr));
    addr.sun_family = AF_UNIX;
    strncpy(addr.sun_path, socket_path.c_str(), sizeof(addr.sun_path) - 1);

    ASSERT_EQ(bind(listen_fd, (struct sockaddr *)&addr, sizeof(addr)), 0)
        << "Failed to bind socket: " << strerror(errno);
    ASSERT_EQ(listen(listen_fd, 1), 0)
        << "Failed to listen on socket: " << strerror(errno);

    std::filesystem::path const dbname =
        std::filesystem::temp_directory_path() / "test_triedb_reconnect.mdb";
    std::filesystem::remove(dbname);
    BOOST_SCOPE_EXIT(&dbname)
    {
        std::filesystem::remove(dbname);
    }
    BOOST_SCOPE_EXIT_END

    int const fd =
        ::open(dbname.c_str(), O_RDWR | O_CREAT | O_TRUNC | O_CLOEXEC, 0644);
    ASSERT_GE(fd, 0) << "Failed to create db file: " << strerror(errno);
    ASSERT_EQ(::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)), 0)
        << "Failed to truncate db file: " << strerror(errno);
    ::close(fd);

    monad::mpt::AsyncIOContext io_ctx{
        monad::mpt::OnDiskDbConfig{.append = false, .dbname_paths = {dbname}}};
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
    close(listen_fd);

    std::unique_ptr<monad::StateSyncServer> sync_server =
        monad::make_statesync_server(monad::StateSyncServerConfig{
            .triedb = &triedb,
            .network = &*net,
            .ro_sq_thread_cpu = std::nullopt,
            .dbname_paths = {dbname}});

    std::this_thread::sleep_for(std::chrono::milliseconds(50));

    close(client_fd);
    client_fd = -1;
    std::this_thread::sleep_for(std::chrono::milliseconds(100));

    sync_server->thread.request_stop();
    sync_server->thread.join();
}
