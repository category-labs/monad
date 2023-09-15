#include <gtest/gtest.h>

#include <monad/config.hpp>

#include <monad/db/in_memory_trie_db.hpp>

#include <monad/execution/replay_block_db.hpp>
#include <monad/execution/test/fakes.hpp>

#include <monad/test/make_db.hpp>

using namespace monad;
using namespace execution;

namespace
{
    class fakeErrorDecompressBlockDb
    {
    public:
        enum class Status
        {
            SUCCESS,
            NO_BLOCK_FOUND,
            DECOMPRESS_ERROR,
            DECODE_ERROR
        };

        block_num_t _last_block_number;

        Status get(block_num_t const, Block &) const
        {
            return Status::DECOMPRESS_ERROR;
        }
    };

    class fakeErrorDecodeBlockDb
    {
    public:
        enum class Status
        {
            SUCCESS,
            NO_BLOCK_FOUND,
            DECOMPRESS_ERROR,
            DECODE_ERROR
        };

        block_num_t _last_block_number;

        Status get(block_num_t const, Block &) const
        {
            return Status::DECODE_ERROR;
        }
    };

    template <class TState, concepts::fork_traits<TState> TTraits>
    struct fakeEmptyTP
    {
        enum class Status
        {
            SUCCESS,
            LATER_NONCE,
            INSUFFICIENT_BALANCE,
            INVALID_GAS_LIMIT,
            BAD_NONCE,
            DEPLOYED_CODE,
        };

        template <class TEvmHost>
        Receipt execute(
            TState &, TEvmHost &, BlockHeader const &,
            Transaction const &) const
        {
            return {};
        }

        Status validate(TState const &, Transaction const &, uint64_t)
        {
            return {};
        }
    };

    template <
        class TState, concepts::fork_traits<TState> TTraits, class TInterpreter>
    struct fakeEmptyEvm
    {
    };

    struct fakeInterpreter
    {
    };

    template <class TTraits, class TState, class TEvm>
    struct fakeEmptyEvmHost
    {
    };

    class fakeEmptyBP
    {
    public:
        template <
            class TMutex, class TTraits, class TxnProcData, class TBlockCache>
        std::vector<Receipt> execute(Block &, Db &, TBlockCache &)
        {
            return {};
        }
    };

    template <class TDb> // Use until Db has state_root call
    class fakeEmptyBPfakeDb
    {
    public:
        template <
            class TMutex, class TTraits, class TxnProcData, class TBlockCache>
        std::vector<Receipt> execute(Block &, TDb &, TBlockCache &)
        {
            return {};
        }
    };

    class fakeEmptyTransactionTrie
    {
    public:
        fakeEmptyTransactionTrie(std::vector<Transaction> const &) {}
        bytes32_t root_hash() const { return bytes32_t{}; }
    };

    class fakeEmptyReceiptTrie
    {
    public:
        fakeEmptyReceiptTrie(std::vector<Receipt> const &) {}
        bytes32_t root_hash() const { return bytes32_t{}; }
    };

    template <
        class TMutex, class TTxnProcessor, class TEvmHost, class TBlockCache>
    struct fakeEmptyFiberData
    {
        Receipt _result{};
        fakeEmptyFiberData(
            Db &, BlockState<TMutex> &, Transaction &, BlockHeader const &,
            TBlockCache &, unsigned int)
        {
        }
        Receipt get_receipt() { return _result; }
        inline void operator()() {}
    };

    using mutex_t = std::shared_mutex;
    using db_t = db::InMemoryTrieDB;
    using state_t = state::State<mutex_t, fake::BlockDb>;
    using traits_t = execution::fake::traits::alpha<state_t>;
    using receipt_collector_t = std::vector<std::vector<Receipt>>;
    using mutex_t = std::shared_mutex;

    using replay_t = ReplayFromBlockDb<db_t,
        mutex_t, fake::BlockDb, fakeEmptyBP, fakeEmptyTransactionTrie,
        fakeEmptyReceiptTrie, receipt_collector_t>;

    using replay_error_decompress_t = ReplayFromBlockDb<db_t,
        mutex_t, fakeErrorDecompressBlockDb, fakeEmptyBP,
        fakeEmptyTransactionTrie, fakeEmptyReceiptTrie, receipt_collector_t>;

    using replay_error_decode_t = ReplayFromBlockDb<db_t,
        mutex_t, fakeErrorDecodeBlockDb, fakeEmptyBP, fakeEmptyTransactionTrie,
        fakeEmptyReceiptTrie, receipt_collector_t>;
}

TEST(ReplayFromBlockDb, invalid_end_block_number)
{
    auto db = test::make_db<db_t>();

    fake::BlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_t replay;

    block_db._last_block_number = 1'000u;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter>(db, block_db, receipt_collector, 100u, 100u);

    EXPECT_EQ(result.status, replay_t::Status::INVALID_END_BLOCK_NUMBER);
    EXPECT_EQ(result.block_number, 100u);
}

TEST(ReplayFromBlockDb, invalid_end_block_number_zero)
{
    auto db = test::make_db<db_t>();

    fake::BlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_t replay;

    block_db._last_block_number = 1'000u;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter>(db, block_db, receipt_collector, 0u, 0u);

    EXPECT_EQ(result.status, replay_t::Status::INVALID_END_BLOCK_NUMBER);
    EXPECT_EQ(result.block_number, 0u);
}

TEST(ReplayFromBlockDb, start_block_number_outside_db)
{
    auto db = test::make_db<db_t>();

    fake::BlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_t replay;

    block_db._last_block_number = 0u;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter>(db, block_db, receipt_collector, 1u);

    EXPECT_EQ(result.status, replay_t::Status::START_BLOCK_NUMBER_OUTSIDE_DB);
    EXPECT_EQ(result.block_number, 1u);
}

TEST(ReplayFromBlockDb, decompress_block_error)
{
    using state_t = state::State<mutex_t, fakeErrorDecompressBlockDb>;
    using traits_t = execution::fake::traits::alpha<state_t>;

    auto db = test::make_db<db_t>();

    fakeErrorDecompressBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_error_decompress_t replay;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter>(db, block_db, receipt_collector, 1u);

    EXPECT_EQ(
        result.status,
        replay_error_decompress_t::Status::DECOMPRESS_BLOCK_ERROR);
    EXPECT_EQ(result.block_number, 1u);
}

TEST(ReplayFromBlockDb, decode_block_error)
{
    using state_t = state::State<mutex_t, fakeErrorDecodeBlockDb>;
    using traits_t = execution::fake::traits::alpha<state_t>;

    auto db = test::make_db<db_t>();

    fakeErrorDecodeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_error_decode_t replay;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter>(db, block_db, receipt_collector, 1u);

    EXPECT_EQ(result.status, replay_error_decode_t::Status::DECODE_BLOCK_ERROR);
    EXPECT_EQ(result.block_number, 1u);
}


TEST(ReplayFromBlockDb, one_block)
{
    using db_t = fake::Db;
    using bp_t = fakeEmptyBPfakeDb<db_t>;
    db_t db;

    using replay_t = ReplayFromBlockDb<db_t,
        mutex_t, fake::BlockDb, bp_t, fakeEmptyTransactionTrie,
        fakeEmptyReceiptTrie, receipt_collector_t>;

    fake::BlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_t replay;

    block_db._last_block_number = 1'000u;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter>(db, block_db, receipt_collector, 100u, 101u);

    EXPECT_EQ(result.status, replay_t::Status::SUCCESS);
    EXPECT_EQ(result.block_number, 100u);
    EXPECT_EQ(receipt_collector.size(), 1u);
}

TEST(ReplayFromBlockDb, run_from_one)
{
    auto db = test::make_db<db_t>();

    fake::BlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_t replay;

    block_db._last_block_number = 1'234u;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter>(db, block_db, receipt_collector, 1u);

    EXPECT_EQ(result.status, replay_t::Status::SUCCESS_END_OF_DB);
    EXPECT_EQ(result.block_number, 1'234u);
    EXPECT_EQ(receipt_collector.size(), 1'234u);
}
