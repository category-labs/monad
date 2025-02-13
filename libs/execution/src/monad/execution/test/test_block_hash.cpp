#include <monad/async/util.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/block_hash_chain.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/test/test_fixtures_gtest.hpp>
#include <test_resource_data.h>

#include <gtest/gtest.h>
#include <stdlib.h>
#include <unistd.h> // for ftruncate

#include <filesystem>
#include <string>

using namespace monad;
using namespace monad::test;

class BlockHashFixture : public test::OnDiskDatabaseFixture
{
    OnDiskMachine machine_;

    std::string_view fixture_template() override
    {
        return "monad_block_hash_test_XXXXXX";
    };

    StateMachine &state_machine() override
    {
        return machine_;
    }

protected:
    bytes32_t commit(
        uint64_t const block_number, uint64_t const round,
        uint64_t const parent_round, bytes32_t mix_hash = {})
    {
        TrieDb tdb{this->db()};
        auto header = MonadConsensusBlockHeader::from_eth_header({
            .prev_randao = mix_hash, // make block hash unique dup round
            .number = block_number,
            .timestamp = round, // make block hash unique on fork
        });
        header.round = round;
        header.qc.vote.round = parent_round;
        if (block_number != 0) {
            tdb.set_block_and_round(block_number - 1, parent_round);
        }
        tdb.commit(StateDeltas{}, Code{}, header);

        auto const encoded_header =
            rlp::encode_block_header(tdb.read_eth_header());
        byte_string_view view{encoded_header};
        return to_bytes(keccak256(view));
    }

    void finalize(uint64_t const block_number, uint64_t const round)
    {
        TrieDb tdb{this->db()};
        tdb.finalize(block_number, round);
    }
};

class BlockHashFixtureDeathTest : public BlockHashFixture
{
};

template <typename BlockHashType>
class BlockHashTest : public BlockHashFixture
{
};

template <typename BlockHashType>
class BlockHashDeathTest : public BlockHashFixtureDeathTest
{
};

using BlockHashTypes = ::testing::Types<BlockHashChain, BlockHashChainCached>;
TYPED_TEST_SUITE(BlockHashTest, BlockHashTypes);
TYPED_TEST_SUITE(BlockHashDeathTest, BlockHashTypes);

TYPED_TEST(BlockHashTest, simple)
{
    std::vector<bytes32_t> finalized;
    finalized.emplace_back(this->commit(0, 0, 0));
    this->finalize(0, 0);
    finalized.emplace_back(this->commit(1, 1, 0));
    finalized.emplace_back(this->commit(2, 2, 1));
    finalized.emplace_back(this->commit(3, 3, 2));

    TypeParam chain(this->db());
    chain.set_block_and_round(3, 3);
    for (uint64_t i = 0; i < finalized.size(); ++i) {
        for (uint64_t reads = 0; reads < 5; ++reads) {
            EXPECT_EQ(finalized[i], chain.get(i));
        }
    }

    // and again with all finalized
    for (uint64_t i = 1; i <= 3; ++i) {
        this->finalize(i, i);
    }
    chain.set_block_and_round(3, 3);
    for (uint64_t i = 0; i < finalized.size(); ++i) {
        for (uint64_t reads = 0; reads < 5; ++reads) {
            EXPECT_EQ(finalized[i], chain.get(i));
        }
    }
}

TYPED_TEST(BlockHashTest, fork)
{
    TypeParam chain(this->db());
    std::vector<bytes32_t> finalized;
    std::vector<bytes32_t> fork;

    finalized.emplace_back(this->commit(0, 0, 0)); // genesis
    this->finalize(0, 0);
    finalized.emplace_back(this->commit(1, 1, 0));
    this->finalize(1, 1);

    // fork after block 1
    fork = finalized;
    fork.emplace_back(this->commit(2, 2, 1));
    fork.emplace_back(this->commit(3, 4, 2));

    finalized.emplace_back(this->commit(2, 3, 1));
    finalized.emplace_back(this->commit(3, 5, 3));

    ASSERT_NE(fork, finalized);
    chain.set_block_and_round(3, 5);
    for (uint64_t i = 0; i < finalized.size(); ++i) {
        EXPECT_EQ(finalized[i], chain.get(i));
    }
    chain.set_block_and_round(3, 4);
    for (uint64_t i = 0; i < fork.size(); ++i) {
        EXPECT_EQ(fork[i], chain.get(i));
    }
}

TYPED_TEST(BlockHashTest, keep_latest_duplicate)
{
    TypeParam chain(this->db());
    std::vector<bytes32_t> finalized;
    finalized.emplace_back(this->commit(0, 0, 0)); // genesis
    this->finalize(0, 0);

    auto const overriden = this->commit(
        1, 1, 0); // don't append, block 1 replaced by duplicate round.
    finalized.emplace_back(this->commit(1, 1, 0, bytes32_t{1337}));
    ASSERT_NE(overriden, finalized.back());
    finalized.emplace_back(this->commit(2, 3, 1));

    chain.set_block_and_round(2, 3);
    for (uint64_t i = 0; i < finalized.size(); ++i) {
        EXPECT_EQ(finalized[i], chain.get(i));
    }
}

TYPED_TEST(BlockHashDeathTest, out_of_bounds)
{
    TypeParam chain(this->db());
    this->commit(0, 0, 0); // genesis
    this->finalize(0, 0);
    for (uint64_t i = 1; i <= 256; ++i) {
        this->commit(i, i, i - 1);
        this->finalize(i, i);
    }
    EXPECT_DEATH(chain.get(0), ".*"); // block and round unset
    chain.set_block_and_round(0, 0);
    EXPECT_TRUE(chain.get(0));
    chain.set_block_and_round(255, 255);
    EXPECT_TRUE(chain.get(0));
    EXPECT_TRUE(chain.get(255));
    EXPECT_DEATH(chain.get(256), ".*");
    chain.set_block_and_round(256, 256);
    EXPECT_TRUE(chain.get(255));
    EXPECT_TRUE(chain.get(256));
    EXPECT_TRUE(chain.get(1));
    EXPECT_DEATH(chain.get(0), ".*");
    EXPECT_DEATH(chain.get(257), ".*");
}

TYPED_TEST(BlockHashTest, bench)
{
    TypeParam chain(this->db());
    this->commit(0, 0, 0); // genesis
    this->finalize(0, 0);
    for (uint64_t i = 1; i <= 253; ++i) {
        this->commit(i, i, i - 1);
        this->finalize(i, i);
    }
    this->commit(254, 254, 253);
    this->commit(255, 255, 254);
    chain.set_block_and_round(255, 255);
    for (unsigned i = 0; i < 100'000; ++i) {
        (void)chain.get(i % 256);
    }
}

TEST_F(BlockHashFixture, init_from_db)
{
    TrieDb tdb{this->db()};

    BlockHashBuffer expected;
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
        expected.set(
            i,
            to_bytes(
                keccak256(rlp::encode_block_header(tdb.read_eth_header()))));
    }

    BlockHashBuffer actual;
    EXPECT_FALSE(init_block_hash_buffer_from_triedb(
        this->db(), 5000 /* invalid start block */, actual));
    EXPECT_TRUE(
        init_block_hash_buffer_from_triedb(this->db(), expected.N, actual));

    for (uint64_t i = 0; i < 256; ++i) {
        EXPECT_EQ(expected.get(i), actual.get(i));
    }
}
