#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <test_resource_data.h>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::test;

TEST(BlockHashBuffer, simple_chain)
{
    BlockHashBufferFinalized buf;
    buf.set(0, bytes32_t{0}); // genesis

    BlockHashChain chain(buf);

    uint64_t round = 1;
    uint64_t parent_round = 0;
    chain.propose(bytes32_t{1}, round, parent_round);
    chain.finalize(round);

    ++round;
    ++parent_round;
    chain.propose(bytes32_t{2}, round, parent_round);
    chain.finalize(round);

    ++round;
    ++parent_round;
    chain.propose(bytes32_t{3}, round, parent_round);
    chain.finalize(round);

    EXPECT_EQ(buf.n(), 4);
    EXPECT_EQ(buf.get(0), bytes32_t{0});
    EXPECT_EQ(buf.get(1), bytes32_t{1});
    EXPECT_EQ(buf.get(2), bytes32_t{2});
    EXPECT_EQ(buf.get(3), bytes32_t{3});
}

TEST(BlockHashBuffer, from_seeded_buf)
{
    BlockHashBufferFinalized buf;
    buf.set(0, bytes32_t{1});
    buf.set(1, bytes32_t{2});

    BlockHashChain chain(buf, 1 /* last_finalized_round */);

    chain.propose(bytes32_t{3}, 2, 1);
    chain.finalize(2);

    EXPECT_EQ(buf.get(0), bytes32_t{1});
    EXPECT_EQ(buf.get(1), bytes32_t{2});
    EXPECT_EQ(buf.get(2), bytes32_t{3});
}

TEST(BlockHashBuffer, fork)
{
    BlockHashBufferFinalized buf;
    buf.set(0, bytes32_t{0}); // genesis

    BlockHashChain chain(buf);

    chain.propose(bytes32_t{1}, 1 /* round */, 0 /* parent_round */);
    chain.finalize(1);

    // fork at block 1
    chain.propose(bytes32_t{2}, 2 /* round */, 1 /* parent_round */);
    chain.propose(bytes32_t{3}, 3 /* round */, 1 /* parent_round */);

    // fork continues on block 2
    chain.propose(bytes32_t{4}, 4 /* round */, 3 /* parent_round */);
    chain.propose(bytes32_t{5}, 5 /* round */, 2 /* parent_round */);

    // check the forks are distinct
    auto const &fork1 = chain.find_chain(4);
    EXPECT_EQ(fork1.n(), 4);
    EXPECT_EQ(fork1.get(0), bytes32_t{0});
    EXPECT_EQ(fork1.get(1), bytes32_t{1});
    EXPECT_EQ(fork1.get(2), bytes32_t{3});
    EXPECT_EQ(fork1.get(3), bytes32_t{4});

    auto const &fork2 = chain.find_chain(5);
    EXPECT_EQ(fork2.n(), 4);
    EXPECT_EQ(fork2.get(0), bytes32_t{0});
    EXPECT_EQ(fork2.get(1), bytes32_t{1});
    EXPECT_EQ(fork2.get(2), bytes32_t{2});
    EXPECT_EQ(fork2.get(3), bytes32_t{5});

    // ... and that the finalized chain is unmodified
    EXPECT_EQ(buf.n(), 2);

    // finalize chain {0, 1, 2, 5}
    chain.finalize(2);
    chain.finalize(5);

    // finalized chain should match fork
    EXPECT_EQ(buf.n(), 4);
    EXPECT_EQ(buf.get(0), bytes32_t{0});
    EXPECT_EQ(buf.get(1), bytes32_t{1});
    EXPECT_EQ(buf.get(2), bytes32_t{2});
    EXPECT_EQ(buf.get(3), bytes32_t{5});
}

TEST(BlockHashBuffer, keep_latest_duplicate)
{
    BlockHashBufferFinalized buf;
    buf.set(0, bytes32_t{0}); // genesis

    BlockHashChain chain(buf);

    chain.propose(bytes32_t{1}, 1 /* round */, 0 /* parent_round */);
    chain.finalize(1);

    chain.propose(bytes32_t{2}, 2 /* round */, 1 /* parent_round */);
    chain.propose(bytes32_t{3}, 3 /* round */, 1 /* parent_round */);
    chain.propose(bytes32_t{4}, 2 /* round */, 1 /* parent_round */);
    chain.finalize(2);

    EXPECT_EQ(buf.n(), 3);
    EXPECT_EQ(buf.get(0), bytes32_t{0});
    EXPECT_EQ(buf.get(1), bytes32_t{1});
    EXPECT_EQ(buf.get(2), bytes32_t{4});
}

TEST(BlockHashBuffer, propose_after_crash)
{
    BlockHashBufferFinalized buf;
    for (uint64_t i = 0; i < 100; ++i) {
        buf.set(i, bytes32_t{i});
    }
    ASSERT_EQ(buf.n(), 100);

    BlockHashChain chain(buf, 99 /* last_finalized_round */);
    auto &buf2 = chain.find_chain(99);
    EXPECT_EQ(&buf, &buf2);

    chain.propose(bytes32_t{100}, 100 /* round */, 99 /* parent_round */);
    chain.finalize(100);
    EXPECT_EQ(buf.n() - 1, 100);

    for (uint64_t i = 0; i < buf.n(); ++i) {
        EXPECT_EQ(bytes32_t{i}, buf.get(i));
    }
}

TEST(BlockHashBufferTest, init_from_db)
{
    auto const path = [] {
        std::filesystem::path dbname(
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "monad_block_hash_buffer_test_XXXXXX");
        int const fd = ::mkstemp((char *)dbname.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(
            -1 !=
            ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
        ::close(fd);
        return dbname;
    }();

    OnDiskMachine machine;
    mpt::Db db{
        machine, mpt::OnDiskDbConfig{.append = false, .dbname_paths = {path}}};
    TrieDb tdb{db};

    BlockHashBufferFinalized expected;
    for (uint64_t i = 0; i < 256; ++i) {
        BlockHeader hdr{.number = i};
        commit_sequential(tdb, {}, {}, hdr);
        expected.set(i, to_bytes(keccak256(rlp::encode_block_header(hdr))));
    }

    BlockHashBufferFinalized actual;
    EXPECT_FALSE(init_block_hash_buffer_from_triedb(
        db, 5000 /* invalid start block */, actual));
    EXPECT_TRUE(init_block_hash_buffer_from_triedb(db, expected.n(), actual));

    for (uint64_t i = 0; i < 256; ++i) {
        EXPECT_EQ(expected.get(i), actual.get(i));
    }
}

TEST(BlockHashBufferDeathTest, bogus_round)
{
    BlockHashBufferFinalized buf;
    for (uint64_t i = 0; i < buf.N; ++i) {
        buf.set(i, bytes32_t{i});
    }

    BlockHashChain chain(buf, buf.n());

    // actual finalized round that is earlier than latest finalized
    EXPECT_DEATH(chain.find_chain(20), ".*");
    EXPECT_DEATH(
        chain.propose(
            bytes32_t{1}, buf.n() + 1 /* round */, 20 /* parent_round */),
        ".*");

    // bogus round
    EXPECT_DEATH(chain.find_chain(3000), ".*");
    EXPECT_DEATH(
        chain.propose(
            bytes32_t{1}, buf.n() + 1 /* round */, 3000 /* parent_round */),
        ".*");
}

TEST(BlockHashBufferDeathTest, double_finalize)
{
    BlockHashBufferFinalized buf;
    buf.set(0, bytes32_t{0}); // genesis

    BlockHashChain chain(buf);

    chain.propose(bytes32_t{1}, 1 /* round */, 0 /* parent_round */);
    chain.finalize(1);
    EXPECT_DEATH(chain.finalize(1), ".*");
}
