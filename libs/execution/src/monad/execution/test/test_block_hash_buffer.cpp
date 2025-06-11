#include <monad/async/util.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/test/resource_owning_fixture.hpp>
#include <test_resource_data.h>

#include <filesystem>
#include <gtest/gtest.h>
#include <stdlib.h>

using namespace monad;
using namespace monad::test;

struct BlockHashBufferFixture : public ResourceOwningFixture
{
};

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

    BlockHashChain chain(buf);

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

TEST(BlockHashBuffer, double_finalize)
{
    BlockHashBufferFinalized buf;
    buf.set(0, bytes32_t{0}); // genesis

    BlockHashChain chain(buf);

    chain.propose(bytes32_t{1}, 1 /* round */, 0 /* parent_round */);
    chain.propose(bytes32_t{1}, 2 /* round */, 1 /* parent_round */);
    chain.finalize(1);
    chain.finalize(1);
    chain.finalize(2);
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

    BlockHashChain chain(buf);
    auto const &buf2 = chain.find_chain(99);
    EXPECT_EQ(&buf, &buf2);

    chain.propose(bytes32_t{100}, 100 /* round */, 99 /* parent_round */);
    chain.finalize(100);
    EXPECT_EQ(buf.n() - 1, 100);

    for (uint64_t i = 0; i < buf.n(); ++i) {
        EXPECT_EQ(bytes32_t{i}, buf.get(i));
    }
}

TEST_F(BlockHashBufferFixture, init_from_db)
{
    auto const path = create_temp_file(8ULL * 1024 * 1024 * 1024);

    OnDiskMachine machine;
    mpt::Db db{
        machine, mpt::OnDiskDbConfig{.append = false, .dbname_paths = {path}}};
    TrieDb tdb{db};

    BlockHashBufferFinalized expected;
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
        expected.set(
            i,
            to_bytes(
                keccak256(rlp::encode_block_header(tdb.read_eth_header()))));
    }

    BlockHashBufferFinalized actual;
    EXPECT_FALSE(init_block_hash_buffer_from_triedb(
        db, 5000 /* invalid start block */, actual));
    EXPECT_TRUE(init_block_hash_buffer_from_triedb(db, expected.n(), actual));

    for (uint64_t i = 0; i < 256; ++i) {
        EXPECT_EQ(expected.get(i), actual.get(i));
    }
}
