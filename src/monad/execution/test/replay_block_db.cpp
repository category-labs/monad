#include <gtest/gtest.h>

#include <monad/config.hpp>

#include <monad/execution/replay_block_db.hpp>

#include <monad/execution/test/fakes.hpp>

#include <monad/logging/monad_log.hpp>

using namespace monad;
using namespace execution;

class fakeBlockDb
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

    Status get(block_num_t const block_number, Block &) const
    {
        if (block_number <= _last_block_number) {
            return Status::SUCCESS;
        }
        else {
            return Status::NO_BLOCK_FOUND;
        }
    }
};

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
        TState &, TEvmHost &, BlockHeader const &, Transaction const &) const
    {
        return {};
    }

    Status validate(TState const &, Transaction const &, uint64_t)
    {
        return {};
    }
};

template <
    class TState, concepts::fork_traits<TState> TTraits,
    class TStaticPrecompiles, class TInterpreter>
struct fakeEmptyEvm
{
};

struct fakeInterpreter {};

template <class TTraits, class TState, class TEvm>
struct fakeEmptyEvmHost
{
};

template <class TExecution>
class fakeEmptyBP
{
public:
    template <class TState, class TFiberData>
    std::vector<Receipt> execute(TState &, Block &)
    {
        return {};
    }
};

template <class TState>
class fakeEmptyStateTrie
{
public:
    bytes32_t incremental_update(TState &) { return bytes32_t{}; }
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
    class TState, concepts::fork_traits<TState> TTraits, class TTxnProcessor,
    class TEvm, class TExecution>
struct fakeEmptyFiberData
{
    Receipt _result{};
    fakeEmptyFiberData(TState &, Transaction const &, BlockHeader const &, int)
    {
    }
    Receipt get_receipt() { return _result; }
    inline void operator()() {}
};

using state_t = execution::fake::State;
using traits_t = execution::fake::traits::alpha<state_t>;
using receipt_collector_t = std::vector<std::vector<Receipt>>;

using replay_t = ReplayFromBlockDb<
    state_t, fakeBlockDb, BoostFiberExecution, fakeEmptyBP, fakeEmptyStateTrie,
    fakeEmptyTransactionTrie, fakeEmptyReceiptTrie, receipt_collector_t,
    log::logger_t>;

using replay_error_decompress_t = ReplayFromBlockDb<
    state_t, fakeErrorDecompressBlockDb, BoostFiberExecution, fakeEmptyBP,
    fakeEmptyStateTrie, fakeEmptyTransactionTrie, fakeEmptyReceiptTrie,
    receipt_collector_t, log::logger_t>;

using replay_error_decode_t = ReplayFromBlockDb<
    state_t, fakeErrorDecodeBlockDb, BoostFiberExecution, fakeEmptyBP,
    fakeEmptyStateTrie, fakeEmptyTransactionTrie, fakeEmptyReceiptTrie,
    receipt_collector_t, log::logger_t>;

TEST(ReplayFromBlockDb, invalid_end_block_number)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_t replay;

    block_db._last_block_number = 1'000u;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter,
        boost::mp11::mp_list<fake::static_precompiles::Echo<traits_t>>>(
        state, state_trie, block_db, receipt_collector, 100u, 100u);

    EXPECT_EQ(result.status, replay_t::Status::INVALID_END_BLOCK_NUMBER);
    EXPECT_EQ(result.block_number, 100u);
}

TEST(ReplayFromBlockDb, invalid_end_block_number_zero)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_t replay;

    block_db._last_block_number = 1'000u;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter,
        boost::mp11::mp_list<fake::static_precompiles::Echo<traits_t>>>(
        state, state_trie, block_db, receipt_collector, 0u, 0u);

    EXPECT_EQ(result.status, replay_t::Status::INVALID_END_BLOCK_NUMBER);
    EXPECT_EQ(result.block_number, 0u);
}

TEST(ReplayFromBlockDb, start_block_number_outside_db)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_t replay;

    block_db._last_block_number = 0u;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter,
        boost::mp11::mp_list<fake::static_precompiles::Echo<traits_t>>>(
        state, state_trie, block_db, receipt_collector, 1u);

    EXPECT_EQ(result.status, replay_t::Status::START_BLOCK_NUMBER_OUTSIDE_DB);
    EXPECT_EQ(result.block_number, 1u);
}

TEST(ReplayFromBlockDb, decompress_block_error)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeErrorDecompressBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_error_decompress_t replay;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter,
        boost::mp11::mp_list<fake::static_precompiles::Echo<traits_t>>>(
        state, state_trie, block_db, receipt_collector, 1u);

    EXPECT_EQ(
        result.status,
        replay_error_decompress_t::Status::DECOMPRESS_BLOCK_ERROR);
    EXPECT_EQ(result.block_number, 1u);
}

TEST(ReplayFromBlockDb, decode_block_error)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeErrorDecodeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_error_decode_t replay;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter,
        boost::mp11::mp_list<fake::static_precompiles::Echo<traits_t>>>(
        state, state_trie, block_db, receipt_collector, 1u);

    EXPECT_EQ(result.status, replay_error_decode_t::Status::DECODE_BLOCK_ERROR);
    EXPECT_EQ(result.block_number, 1u);
}

TEST(ReplayFromBlockDb, one_block)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_t replay;

    block_db._last_block_number = 1'000u;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter,
        boost::mp11::mp_list<fake::static_precompiles::Echo<traits_t>>>(
        state, state_trie, block_db, receipt_collector, 100u, 101u);

    EXPECT_EQ(result.status, replay_t::Status::SUCCESS);
    EXPECT_EQ(result.block_number, 100u);
    EXPECT_EQ(receipt_collector.size(), 1u);
}

TEST(ReplayFromBlockDb, run_from_zero)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_t replay;

    block_db._last_block_number = 1'234u;

    auto result = replay.run<
        traits_t,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeEmptyFiberData,
        fakeInterpreter,
        boost::mp11::mp_list<fake::static_precompiles::Echo<traits_t>>>(
        state, state_trie, block_db, receipt_collector, 0u);

    EXPECT_EQ(result.status, replay_t::Status::SUCCESS_END_OF_DB);
    EXPECT_EQ(result.block_number, 1'234u);
    EXPECT_EQ(receipt_collector.size(), 1'235u);
}
