#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <monad/async/config.hpp>
#include <monad/async/io.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <atomic>
#include <chrono>
#include <cstddef>
#include <future>
#include <iostream>
#include <latch>
#include <sstream>
#include <string>
#include <thread>
#include <utility>

using namespace MONAD_ASYNC_NAMESPACE;
using namespace MONAD_MPT_NAMESPACE;

struct ReadOnlyDBTest
    : public monad::test::FillDBWithChunksGTest<
          monad::test::FillDBWithChunksConfig{.chunks_to_fill = 1}>
{
};

inline std::string print(monad::byte_string_view arr)
{
    std::stringstream s;
    s << "0x" << std::hex;
    s.fill('0');
    for (auto const &c : arr) {
        s.width(2);
        s << (unsigned)c;
    }
    return std::move(s).str();
}

TEST_F(ReadOnlyDBTest, read_only_dbs_track_writable_db)
{
    auto pool = state()->pool.clone_as_read_only();
    // Can only have one AsyncIO instance per kernel thread
    std::latch do_append(1);
    std::latch append_done(1);
    std::latch second_block_checked(1);
    std::atomic<int> done{0};
    auto fut = std::async(std::launch::async, [&] {
        monad::io::Ring ring{2};
        monad::io::Buffers rwbuf{monad::io::make_buffers_for_read_only(
            ring,
            2,
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE)};
        MONAD_ASYNC_NAMESPACE::AsyncIO io{pool, rwbuf};
        monad::test::MerkleCompute const comp;
        monad::test::StateMachineAlwaysMerkle sm;
        monad::test::UpdateAux<void> aux{&io};
        auto const latest_version = aux.db_history_max_version();
        ASSERT_EQ(
            state()->aux.get_latest_root_offset(),
            aux.get_latest_root_offset());
        Node::UniquePtr root{read_node_blocking(
            aux, aux.get_latest_root_offset(), latest_version)};
        auto root_hash = [&] {
            monad::byte_string res(32, 0);
            sm.get_compute().compute(res.data(), root.get());
            return res;
        };
        std::cout << "   Root hash with one chunk is " << print(root_hash())
                  << std::endl;
        EXPECT_EQ(state()->root_hash(), root_hash());
        done.fetch_add(1, std::memory_order_acq_rel);

        // Have the main thread add a chunk
        do_append.count_down();
        append_done.wait();
        int n = 1;
        auto read_chunk = [&] {
            root = Node::UniquePtr{read_node_blocking(
                aux, aux.get_latest_root_offset(), latest_version)};
            n++;
            std::cout << "   Root hash with " << n << " chunks is "
                      << print(root_hash()) << std::endl;
            done.fetch_add(1, std::memory_order_acq_rel);
        };
        auto last_root_offset = aux.get_latest_root_offset();
        ASSERT_EQ(state()->aux.get_latest_root_offset(), last_root_offset);
        read_chunk();
        EXPECT_EQ(state()->root_hash(), root_hash());
        second_block_checked.count_down();

        // Now try to keep up ...
        while (done.load(std::memory_order_acquire) > 0) {
            auto const root_offset = aux.get_latest_root_offset();
            if (root_offset == last_root_offset) {
                std::this_thread::yield();
                continue;
            }
            last_root_offset = root_offset;
            read_chunk();
        }
    });
    do_append.wait();
    std::cout << "   Appending a second chunk ... " << std::endl;
    state()->ensure_total_chunks(2);
    append_done.count_down();
    second_block_checked.wait();
    std::cout << "   Appending more chunks ... " << std::endl;
    auto begin = std::chrono::steady_clock::now();
    int n = 3;
    while (std::chrono::steady_clock::now() - begin <
           std::chrono::seconds(10)) {
        state()->ensure_total_chunks(size_t(n++));
    }
    while (done < n - 1) {
        std::this_thread::yield();
    }
    done = -99;
    fut.get();
}
