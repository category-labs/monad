#include <category/async/util.hpp>
#include <category/core/blake3.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/core/monad_block.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/util.hpp>
#include <test_resource_data.h>

#include <gtest/gtest.h>
#include <stdlib.h>
#include <unistd.h> // for ftruncate

#include <filesystem>

using namespace monad;
using namespace monad::test;

namespace
{
    bytes32_t dummy_block_id(uint64_t const seed)
    {
        return to_bytes(
            blake3(mpt::serialize_as_big_endian<sizeof(seed)>(seed)));
    }
}

TEST(BlockHashBuffer, simple_chain)
{
    BlockHashBufferFinalized buf;
    buf.set(0, bytes32_t{0}); // genesis

    BlockHashChain chain(buf);

    uint64_t seed = 0;
    auto parent_id = dummy_block_id(seed);
    auto block_id = dummy_block_id(seed);
    chain.propose(bytes32_t{1}, 1, block_id, parent_id);
    chain.finalize(block_id);

    ++seed;
    parent_id = block_id;
    block_id = dummy_block_id(seed);
    chain.propose(bytes32_t{2}, 2, block_id, parent_id);
    chain.finalize(block_id);

    ++seed;
    parent_id = block_id;
    block_id = dummy_block_id(seed);
    chain.propose(bytes32_t{3}, 3, block_id, parent_id);
    chain.finalize(block_id);

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

    chain.propose(bytes32_t{3}, 2, dummy_block_id(2), dummy_block_id(1));
    chain.finalize(dummy_block_id(2));

    EXPECT_EQ(buf.get(0), bytes32_t{1});
    EXPECT_EQ(buf.get(1), bytes32_t{2});
    EXPECT_EQ(buf.get(2), bytes32_t{3});
}

TEST(BlockHashBuffer, fork)
{
    BlockHashBufferFinalized buf;
    buf.set(0, bytes32_t{0}); // genesis
    EXPECT_EQ(buf.n(), 1);

    BlockHashChain chain(buf);

    chain.propose(bytes32_t{1}, 1, dummy_block_id(1), dummy_block_id(0));
    chain.finalize(dummy_block_id(1)); // finalize block 1
    EXPECT_EQ(buf.n(), 2);

    // fork at block 2
    chain.propose(bytes32_t{2}, 2, dummy_block_id(2), dummy_block_id(1));
    chain.propose(bytes32_t{3}, 2, dummy_block_id(3), dummy_block_id(1));

    // fork continues on block 3
    chain.propose(bytes32_t{4}, 3, dummy_block_id(4), dummy_block_id(3));
    chain.propose(bytes32_t{5}, 3, dummy_block_id(5), dummy_block_id(2));

    // check the forks are distinct
    auto const &fork1 = chain.find_chain(dummy_block_id(4));
    EXPECT_EQ(fork1.n(), 4);
    EXPECT_EQ(fork1.get(0), bytes32_t{0});
    EXPECT_EQ(fork1.get(1), bytes32_t{1});
    EXPECT_EQ(fork1.get(2), bytes32_t{3});
    EXPECT_EQ(fork1.get(3), bytes32_t{4});

    auto const &fork2 = chain.find_chain(dummy_block_id(5));
    EXPECT_EQ(fork2.n(), 4);
    EXPECT_EQ(fork2.get(0), bytes32_t{0});
    EXPECT_EQ(fork2.get(1), bytes32_t{1});
    EXPECT_EQ(fork2.get(2), bytes32_t{2});
    EXPECT_EQ(fork2.get(3), bytes32_t{5});

    // ... and that the finalized chain is unmodified
    EXPECT_EQ(buf.n(), 2);

    // finalize chain {0, 1, 2, 5}
    chain.finalize(dummy_block_id(2));
    chain.finalize(dummy_block_id(5));

    // finalized chain should match fork
    EXPECT_EQ(buf.n(), 4);
    EXPECT_EQ(buf.get(0), bytes32_t{0});
    EXPECT_EQ(buf.get(1), bytes32_t{1});
    EXPECT_EQ(buf.get(2), bytes32_t{2});
    EXPECT_EQ(buf.get(3), bytes32_t{5});
}

TEST(BlockHashBuffer, duplicate_proposals)
{
    BlockHashBufferFinalized buf;
    buf.set(0, bytes32_t{0}); // genesis

    BlockHashChain chain(buf);

    chain.propose(bytes32_t{1}, 1, dummy_block_id(1), dummy_block_id(0));
    chain.finalize(dummy_block_id(1));

    chain.propose(
        bytes32_t{2}, 2, dummy_block_id(2), dummy_block_id(1)); // will finalize
    chain.propose(bytes32_t{3}, 2, dummy_block_id(3), dummy_block_id(1));
    chain.propose(bytes32_t{4}, 2, dummy_block_id(4), dummy_block_id(1));

    chain.propose(bytes32_t{5}, 3, dummy_block_id(5), dummy_block_id(1));
    chain.propose(
        bytes32_t{6}, 3, dummy_block_id(6), dummy_block_id(2)); // will finalize
    chain.finalize(dummy_block_id(2));

    EXPECT_EQ(buf.n(), 3);
    EXPECT_EQ(buf.get(0), bytes32_t{0});
    EXPECT_EQ(buf.get(1), bytes32_t{1});
    EXPECT_EQ(buf.get(2), bytes32_t{2});

    chain.finalize(dummy_block_id(6));
    EXPECT_EQ(buf.get(3), bytes32_t{6});
}

TEST(BlockHashBuffer, propose_after_crash)
{
    BlockHashBufferFinalized buf;
    for (uint64_t i = 0; i < 100; ++i) {
        buf.set(i, bytes32_t{i});
    }
    ASSERT_EQ(buf.n(), 100);

    BlockHashChain chain(buf);
    bytes32_t const nonexist{};
    auto const &buf2 = chain.find_chain(nonexist);
    EXPECT_EQ(&buf, &buf2);

    chain.propose(bytes32_t{100}, 100, dummy_block_id(100), dummy_block_id(99));
    chain.finalize(dummy_block_id(100));
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

    std::filesystem::remove(path);
}
