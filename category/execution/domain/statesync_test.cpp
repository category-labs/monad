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

#include <category/async/config.hpp>
#include <category/async/util.hpp>
#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/chain_id.hpp>
#include <category/execution/domain/derive_domain_block.hpp>
#include <category/execution/domain/domain_block.hpp>
#include <category/execution/domain/executor.hpp>
#include <category/execution/domain/spoke.hpp>
#include <category/execution/domain/statesync.hpp>
#include <category/execution/domain/statesync_listener.hpp>
#include <category/execution/domain/system_transaction.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/db_snapshot.h>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <functional>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <thread>
#include <utility>
#include <vector>

#include <fcntl.h>
#include <stdlib.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <unistd.h>

using namespace monad;
using namespace monad::domain;
using namespace monad::literals;

namespace
{
    constexpr uint64_t DOMAIN = 0x510000004eaf;
    constexpr monad_revision REVISION = MONAD_TEN;
    constexpr Address HUB = 0x00000000000000000000000000000000000000ab_address;

    // An EIP-1559 transaction of DOMAIN (nonce 0, gas 100'000, to 0xabc,
    // data 0x0102) signed by secp256k1 key 0x42, by eth-account.
    Transaction signed_transaction()
    {
        auto const encoded = *from_hex(
            "02f87086510000004eaf8080850ba43b7400830186a094000000000000000000"
            "0000000000000000000abc80820102c080a03524410eec196ed020b64c6e2b16"
            "b18249621686c02655d096b510644ee71a27a05400ac6a0ec2d6bee704ab7aff"
            "e172fe9b86521a26d164b21bc8966dc9569f05");
        byte_string_view view{encoded};
        return rlp::decode_transaction(view).value();
    }

    Transaction delivery(uint64_t const nonce)
    {
        return make_domain_system_transaction(
            DOMAIN,
            DOMAIN_SPOKE,
            DOMAIN_GAS_PRICE,
            300'000,
            DOMAIN & NETWORK_CHAIN_ID_MASK,
            Address{0x1111},
            Address{0x2222},
            byte_string{0xca, 0xfe},
            nonce);
    }

    DerivedDomainBlock
    block(uint64_t const number, std::vector<Transaction> txs)
    {
        std::vector<Address> senders;
        for (auto const &tx : txs) {
            auto const sender = recover_sender(tx);
            MONAD_ASSERT(sender.has_value());
            senders.push_back(*sender);
        }
        return DerivedDomainBlock{
            .number = number,
            .l1_block_number = 10 + number,
            .timestamp = 1'000 + number,
            .prev_randao = bytes32_t{0x77},
            .slot_number = std::nullopt,
            .transactions = std::move(txs),
            .senders = std::move(senders)};
    }

    struct TestL1Chain final : MonadChain
    {
        uint256_t get_chain_id() const override
        {
            return DOMAIN & NETWORK_CHAIN_ID_MASK;
        }

        monad_revision get_monad_revision(uint64_t) const override
        {
            return REVISION;
        }

        GenesisState get_genesis_state() const override
        {
            return GenesisState{};
        }
    };

    // One frame of a statesync reply.
    struct Frame
    {
        uint8_t tag;
        uint8_t type;
        uint16_t shard;
        byte_string payload;
    };

    constexpr uint8_t FRAME_DATA = 1;
    constexpr uint8_t FRAME_FAILED = 3;

    bool receive_all(int const fd, uint8_t *const data, size_t const size)
    {
        for (size_t done = 0; done < size;) {
            ssize_t const n = ::recv(fd, data + done, size - done, 0);
            if (n <= 0) {
                return false;
            }
            done += static_cast<size_t>(n);
        }
        return true;
    }

    void send_all(int const fd, uint8_t const *const data, size_t const size)
    {
        for (size_t done = 0; done < size;) {
            ssize_t const n =
                ::send(fd, data + done, size - done, MSG_NOSIGNAL);
            if (n <= 0) {
                return;
            }
            done += static_cast<size_t>(n);
        }
    }

    void send_frame(int const fd, Frame const &frame)
    {
        std::array<uint8_t, 8> header{};
        header[0] = frame.tag;
        header[1] = frame.type;
        header[2] = static_cast<uint8_t>(frame.shard >> 8);
        header[3] = static_cast<uint8_t>(frame.shard);
        header[4] = static_cast<uint8_t>(frame.payload.size() >> 24);
        header[5] = static_cast<uint8_t>(frame.payload.size() >> 16);
        header[6] = static_cast<uint8_t>(frame.payload.size() >> 8);
        header[7] = static_cast<uint8_t>(frame.payload.size());
        send_all(fd, header.data(), header.size());
        send_all(fd, frame.payload.data(), frame.payload.size());
    }

    // A connected pair of stream sockets, closed with the object.
    struct SocketPair
    {
        int fds[2]{-1, -1};

        SocketPair()
        {
            MONAD_ASSERT(::socketpair(AF_UNIX, SOCK_STREAM, 0, fds) == 0);
        }

        ~SocketPair()
        {
            close(0);
            close(1);
        }

        void close(size_t const i)
        {
            if (fds[i] != -1) {
                ::close(fds[i]);
                fds[i] = -1;
            }
        }
    };

    class DomainStatesyncTest : public ::testing::Test
    {
    protected:
        // Rewrites a reply's frames before the client sees them.
        using Tamper = std::function<void(std::vector<Frame> &)>;

        std::filesystem::path dir_;
        std::string source_path_;
        std::string target_path_;
        std::optional<mpt::Db> source_;
        std::vector<DerivedDomainBlock> blocks_;
        TestL1Chain l1_chain_;
        vm::VM vm_;
        fiber::PriorityPool pool_{1, 1};

        void SetUp() override
        {
            std::string pattern =
                (MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                 "private_domain_statesync_XXXXXX")
                    .string();
            ASSERT_NE(::mkdtemp(pattern.data()), nullptr);
            dir_ = pattern;
            source_path_ = create_file("source.db");
            target_path_ = create_file("target.db");
            source_.emplace(
                std::make_unique<MonadOnDiskMachine>(), config(source_path_));

            // Five blocks: the domain's state at block 3 differs from its
            // state at its latest block.
            blocks_.push_back(block(0, {}));
            blocks_.push_back(block(1, {signed_transaction()}));
            blocks_.push_back(block(2, {delivery(0)}));
            blocks_.push_back(block(3, {}));
            blocks_.push_back(block(4, {delivery(1)}));
            PrivateDomainExecutor executor{
                l1_chain_, DOMAIN, HUB, *source_, vm_, pool_};
            for (auto const &derived : blocks_) {
                ASSERT_TRUE(executor.execute(derived).has_value());
            }
        }

        void TearDown() override
        {
            source_.reset();
            std::filesystem::remove_all(dir_);
        }

        std::string create_file(char const *const name)
        {
            auto const path = (dir_ / name).string();
            int const fd =
                ::open(path.c_str(), O_CREAT | O_WRONLY | O_CLOEXEC, 0644);
            MONAD_ASSERT(fd != -1);
            MONAD_ASSERT(
                ::ftruncate(
                    fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)) != -1);
            ::close(fd);
            return path;
        }

        static mpt::OnDiskDbConfig config(std::string const &path)
        {
            mpt::OnDiskDbConfig result;
            result.sq_thread_cpu = std::nullopt;
            result.dbname_path = path;
            result.chunk_capacity = 24;
            return result;
        }

        static BlockHeader read_header(mpt::Db &db, uint64_t const number)
        {
            auto const cursor = db.find(
                mpt::concat(
                    FINALIZED_NIBBLE, mpt::NibblesView{block_header_nibbles}),
                number);
            MONAD_ASSERT(cursor.has_value());
            byte_string_view encoded{cursor.value().node->value()};
            auto header = rlp::decode_block_header(encoded);
            MONAD_ASSERT(header.has_value());
            return std::move(header).value();
        }

        static bytes32_t block_hash(BlockHeader const &header)
        {
            return to_bytes(keccak256(rlp::encode_block_header(header)));
        }

        bytes32_t source_hash(uint64_t const number)
        {
            return block_hash(read_header(*source_, number));
        }

        // Syncs block `number` from the source db, which stays open for
        // writing, expecting `hash`. Returns the client's and the server's
        // results.
        std::pair<Result<void>, Result<void>> sync(
            uint64_t const number, bytes32_t const &hash,
            uint64_t const served_domain = DOMAIN, Tamper const &tamper = {})
        {
            SocketPair server;
            Result<void> served{outcome::success()};
            std::thread server_thread{[&] {
                served = serve_domain_state(
                    server.fds[1], served_domain, source_path_);
                server.close(1);
            }};
            // With a tamper, the client talks to a proxy that takes the
            // whole reply and sends on what the tamper leaves of it.
            SocketPair proxy;
            std::thread proxy_thread;
            int client_fd = server.fds[0];
            if (tamper) {
                client_fd = proxy.fds[0];
                proxy_thread = std::thread{[&] {
                    std::array<uint8_t, 24> request{};
                    if (!receive_all(
                            proxy.fds[1], request.data(), request.size())) {
                        return;
                    }
                    send_all(server.fds[0], request.data(), request.size());
                    std::vector<Frame> frames;
                    while (true) {
                        std::array<uint8_t, 8> header{};
                        if (!receive_all(
                                server.fds[0], header.data(), header.size())) {
                            break;
                        }
                        Frame frame{
                            .tag = header[0],
                            .type = header[1],
                            .shard = static_cast<uint16_t>(
                                (header[2] << 8) | header[3]),
                            .payload = byte_string(
                                load_be_unsafe<uint32_t>(header.data() + 4),
                                0)};
                        if (!receive_all(
                                server.fds[0],
                                frame.payload.data(),
                                frame.payload.size())) {
                            break;
                        }
                        bool const last = frame.tag != FRAME_DATA;
                        frames.push_back(std::move(frame));
                        if (last) {
                            break;
                        }
                    }
                    tamper(frames);
                    for (auto const &frame : frames) {
                        send_frame(proxy.fds[1], frame);
                    }
                    proxy.close(1);
                }};
            }
            auto synced = sync_domain_state(
                client_fd, DOMAIN, number, hash, config(target_path_));
            server_thread.join();
            if (proxy_thread.joinable()) {
                proxy_thread.join();
            }
            return {std::move(synced), std::move(served)};
        }
    };
}

TEST_F(DomainStatesyncTest, syncs_the_state_of_a_block)
{
    auto const [synced, served] = sync(3, source_hash(3));
    ASSERT_TRUE(served.has_value());
    ASSERT_TRUE(synced.has_value());

    // The synced db is the domain's as of block 3: executing block 4 on it
    // yields the block the source has.
    auto target_config = config(target_path_);
    target_config.append = true;
    mpt::Db target{target_config};
    EXPECT_EQ(target.get_latest_finalized_version(), 3);
    EXPECT_EQ(read_header(target, 3), read_header(*source_, 3));
    PrivateDomainExecutor executor{l1_chain_, DOMAIN, HUB, target, vm_, pool_};
    EXPECT_EQ(executor.next_block(), 4);
    ASSERT_TRUE(executor.execute(blocks_[4]).has_value());
    EXPECT_EQ(read_header(target, 4), read_header(*source_, 4));
}

TEST_F(DomainStatesyncTest, syncs_the_latest_block)
{
    auto const [synced, served] = sync(4, source_hash(4));
    ASSERT_TRUE(served.has_value());
    ASSERT_TRUE(synced.has_value());

    auto target_config = config(target_path_);
    target_config.append = true;
    mpt::Db target{target_config};
    PrivateDomainExecutor executor{l1_chain_, DOMAIN, HUB, target, vm_, pool_};
    EXPECT_EQ(executor.next_block(), 5);
    // Both continue with the same block.
    auto const next = block(5, {});
    PrivateDomainExecutor source_executor{
        l1_chain_, DOMAIN, HUB, *source_, vm_, pool_};
    ASSERT_TRUE(executor.execute(next).has_value());
    ASSERT_TRUE(source_executor.execute(next).has_value());
    EXPECT_EQ(read_header(target, 5), read_header(*source_, 5));
}

TEST_F(DomainStatesyncTest, rejects_a_block_with_another_hash)
{
    // The state of block 3 under the attested hash of block 4.
    auto const [synced, served] = sync(3, source_hash(4));
    EXPECT_TRUE(served.has_value());
    ASSERT_TRUE(synced.has_error());
    EXPECT_EQ(synced.error(), StatesyncError::WrongBlockHash);
}

TEST_F(DomainStatesyncTest, a_peer_of_another_domain_refuses)
{
    auto const [synced, served] = sync(3, source_hash(3), DOMAIN + 1);
    ASSERT_TRUE(served.has_error());
    EXPECT_EQ(served.error(), StatesyncError::WrongDomain);
    ASSERT_TRUE(synced.has_error());
    EXPECT_EQ(synced.error(), StatesyncError::Unavailable);
}

TEST_F(DomainStatesyncTest, a_peer_without_the_block_refuses)
{
    auto const [synced, served] = sync(9, source_hash(4));
    ASSERT_TRUE(served.has_error());
    EXPECT_EQ(served.error(), StatesyncError::Unavailable);
    ASSERT_TRUE(synced.has_error());
    EXPECT_EQ(synced.error(), StatesyncError::Unavailable);
}

TEST_F(DomainStatesyncTest, rejects_a_state_with_another_root)
{
    // Without its storage the state is not the header's.
    auto const [synced, served] =
        sync(3, source_hash(3), DOMAIN, [](std::vector<Frame> &frames) {
            std::erase_if(frames, [](Frame const &frame) {
                return frame.tag == FRAME_DATA &&
                       frame.type == MONAD_SNAPSHOT_STORAGE;
            });
        });
    EXPECT_TRUE(served.has_value());
    ASSERT_TRUE(synced.has_error());
    EXPECT_EQ(synced.error(), StatesyncError::WrongStateRoot);
}

TEST_F(DomainStatesyncTest, rejects_an_earlier_header_the_state_does_not_hold)
{
    // Block 2's header, which the snapshot of block 3 carries in shard 1,
    // with another gas limit.
    auto forged = read_header(*source_, 2);
    forged.gas_limit += 1;
    auto const [synced, served] =
        sync(3, source_hash(3), DOMAIN, [&forged](std::vector<Frame> &frames) {
            byte_string stream;
            std::erase_if(frames, [&stream](Frame const &frame) {
                bool const header = frame.tag == FRAME_DATA &&
                                    frame.type == MONAD_SNAPSHOT_ETH_HEADER &&
                                    frame.shard == 1;
                if (header) {
                    stream += frame.payload;
                }
                return header;
            });
            // The stream is its header, then the block header.
            ASSERT_GT(stream.size(), sizeof(monad_snapshot_stream_header));
            stream.resize(sizeof(monad_snapshot_stream_header));
            stream += rlp::encode_block_header(forged);
            frames.insert(
                frames.begin(),
                Frame{
                    .tag = FRAME_DATA,
                    .type = MONAD_SNAPSHOT_ETH_HEADER,
                    .shard = 1,
                    .payload = std::move(stream)});
        });
    EXPECT_TRUE(served.has_value());
    ASSERT_TRUE(synced.has_error());
    EXPECT_EQ(synced.error(), StatesyncError::WrongBlockHistory);
}

TEST_F(DomainStatesyncTest, a_reply_that_ends_in_failure_is_not_loaded)
{
    auto const [synced, served] =
        sync(3, source_hash(3), DOMAIN, [](std::vector<Frame> &frames) {
            ASSERT_FALSE(frames.empty());
            frames.back().tag = FRAME_FAILED;
        });
    ASSERT_TRUE(synced.has_error());
    EXPECT_EQ(synced.error(), StatesyncError::Unavailable);
}

TEST_F(DomainStatesyncTest, a_reply_that_is_cut_off_is_not_loaded)
{
    auto const [synced, served] =
        sync(3, source_hash(3), DOMAIN, [](std::vector<Frame> &frames) {
            ASSERT_GT(frames.size(), 2);
            frames.resize(frames.size() / 2);
        });
    ASSERT_TRUE(synced.has_error());
    EXPECT_EQ(synced.error(), StatesyncError::Connection);
}

TEST_F(DomainStatesyncTest, a_client_that_leaves_does_not_stop_the_server)
{
    SocketPair pair;
    std::array<uint8_t, 24> request{0x4d, 0x44, 0x53, 0x53, 0, 0, 0, 1};
    store_be(request.data() + 8, DOMAIN);
    store_be(request.data() + 16, uint64_t{3});
    send_all(pair.fds[0], request.data(), request.size());
    pair.close(0);
    auto const served = serve_domain_state(pair.fds[1], DOMAIN, source_path_);
    ASSERT_TRUE(served.has_error());
    EXPECT_EQ(served.error(), StatesyncError::Connection);
}

TEST_F(DomainStatesyncTest, the_listener_serves_an_allowed_peer)
{
    StatesyncListener const listener{
        "127.0.0.1:0", {"127.0.0.1"}, DOMAIN, source_path_};
    auto const fd =
        connect_statesync_peer("127.0.0.1:" + std::to_string(listener.port()));
    ASSERT_TRUE(fd.has_value());
    auto const synced = sync_domain_state(
        fd.value(), DOMAIN, 3, source_hash(3), config(target_path_));
    ::close(fd.value());
    ASSERT_TRUE(synced.has_value());

    // And the next one.
    auto const second_path = create_file("second.db");
    auto const second =
        connect_statesync_peer("127.0.0.1:" + std::to_string(listener.port()));
    ASSERT_TRUE(second.has_value());
    EXPECT_TRUE(
        sync_domain_state(
            second.value(), DOMAIN, 4, source_hash(4), config(second_path))
            .has_value());
    ::close(second.value());
}

TEST_F(DomainStatesyncTest, the_listener_answers_no_other_peer)
{
    StatesyncListener const listener{
        "127.0.0.1:0", {"127.0.0.2", "::1"}, DOMAIN, source_path_};
    auto const fd =
        connect_statesync_peer("127.0.0.1:" + std::to_string(listener.port()));
    ASSERT_TRUE(fd.has_value());
    auto const synced = sync_domain_state(
        fd.value(), DOMAIN, 3, source_hash(3), config(target_path_));
    ::close(fd.value());
    ASSERT_TRUE(synced.has_error());
    EXPECT_EQ(synced.error(), StatesyncError::Connection);
}

TEST_F(DomainStatesyncTest, the_listener_serves_nothing_before_the_domain_db)
{
    StatesyncListener const listener{
        "127.0.0.1:0", {"127.0.0.1"}, DOMAIN, dir_ / "none.db"};
    auto const fd =
        connect_statesync_peer("127.0.0.1:" + std::to_string(listener.port()));
    ASSERT_TRUE(fd.has_value());
    auto const synced = sync_domain_state(
        fd.value(), DOMAIN, 3, source_hash(3), config(target_path_));
    ::close(fd.value());
    ASSERT_TRUE(synced.has_error());
    EXPECT_EQ(synced.error(), StatesyncError::Connection);
}

TEST_F(DomainStatesyncTest, addresses_must_be_numeric)
{
    EXPECT_THROW(
        (StatesyncListener{"localhost:0", {}, DOMAIN, source_path_}),
        std::runtime_error);
    EXPECT_THROW(
        (StatesyncListener{"127.0.0.1", {}, DOMAIN, source_path_}),
        std::runtime_error);
    EXPECT_THROW(
        (StatesyncListener{"127.0.0.1:0", {"peer"}, DOMAIN, source_path_}),
        std::runtime_error);
    EXPECT_TRUE(connect_statesync_peer("localhost:1").has_error());
}
