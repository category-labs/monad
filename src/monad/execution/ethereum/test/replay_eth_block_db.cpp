#include <gtest/gtest.h>

#include <monad/config.hpp>

#include <monad/execution/replay_block_db.hpp>

#include <monad/execution/test/fakes.hpp>

using empty_list_t = boost::mp11::mp_list<>;

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

template <
    class TState, concepts::fork_traits<TState> TTraits,
    class TStaticPrecompiles, class TInterpreter>
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
    class TState, concepts::fork_traits<TState> TTraits, class TTxnProcessor,
    class TEvm, class TExecution>
struct fakeReceiptFiberData
{
    Receipt _result{.status = TTraits::last_block_number};
    fakeReceiptFiberData() {}
    fakeReceiptFiberData(
        TState &, Transaction const &, BlockHeader const &, int)
    {
    }
    Receipt get_receipt() { return _result; }
    inline void operator()() {}
};

template <class TExecution>
class fakeReceiptBP
{
public:
    template <class TState, class TFiberData>
    std::vector<Receipt> execute(TState &, Block &)
    {
        std::vector<TFiberData> data{{}};
        std::vector<Receipt> r;
        for (auto &d : data) {
            r.push_back(d.get_receipt());
        }
        return r;
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

using eth_start_fork = fork_traits::frontier;

using state_t = execution::fake::State;
using receipt_collector_t = std::vector<std::vector<Receipt>>;

using replay_eth_t = ReplayFromBlockDb<
    state_t, fakeBlockDb, BoostFiberExecution, fakeReceiptBP,
    fakeEmptyStateTrie, fakeEmptyTransactionTrie, fakeEmptyReceiptTrie,
    receipt_collector_t>;

using replay_eth_error_decompress_t = ReplayFromBlockDb<
    state_t, fakeErrorDecompressBlockDb, BoostFiberExecution, fakeReceiptBP,
    fakeEmptyStateTrie, fakeEmptyTransactionTrie, fakeEmptyReceiptTrie,
    receipt_collector_t>;

using replay_eth_error_decode_t = ReplayFromBlockDb<
    state_t, fakeErrorDecodeBlockDb, BoostFiberExecution, fakeReceiptBP,
    fakeEmptyStateTrie, fakeEmptyTransactionTrie, fakeEmptyReceiptTrie,
    receipt_collector_t>;

TEST(ReplayFromBlockDb_Eth, invalid_end_block_number)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_eth_t replay_eth;

    block_db._last_block_number = 1'000u;

    auto result = replay_eth.run<
        eth_start_fork,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeReceiptFiberData,
        fakeInterpreter,
        empty_list_t>(
        state, state_trie, block_db, receipt_collector, 100u, 100u);

    EXPECT_EQ(result.status, replay_eth_t::Status::INVALID_END_BLOCK_NUMBER);
    EXPECT_EQ(result.block_number, 100u);
}

TEST(ReplayFromBlockDb_Eth, invalid_end_block_number_zero)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_eth_t replay_eth;

    block_db._last_block_number = 1'000u;

    auto result = replay_eth.run<
        eth_start_fork,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeReceiptFiberData,
        fakeInterpreter,
        empty_list_t>(state, state_trie, block_db, receipt_collector, 0u, 0u);

    EXPECT_EQ(result.status, replay_eth_t::Status::INVALID_END_BLOCK_NUMBER);
    EXPECT_EQ(result.block_number, 0u);
}

TEST(ReplayFromBlockDb_Eth, start_block_number_outside_db)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_eth_t replay_eth;

    block_db._last_block_number = 0u;

    auto result = replay_eth.run<
        eth_start_fork,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeReceiptFiberData,
        fakeInterpreter,
        empty_list_t>(state, state_trie, block_db, receipt_collector, 1u);

    EXPECT_EQ(
        result.status, replay_eth_t::Status::START_BLOCK_NUMBER_OUTSIDE_DB);
    EXPECT_EQ(result.block_number, 1u);
}

TEST(ReplayFromBlockDb_Eth, decompress_block_error)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeErrorDecompressBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_eth_error_decompress_t replay_eth;

    auto result = replay_eth.run<
        eth_start_fork,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeReceiptFiberData,
        fakeInterpreter,
        empty_list_t>(state, state_trie, block_db, receipt_collector, 1u);

    EXPECT_EQ(
        result.status,
        replay_eth_error_decompress_t::Status::DECOMPRESS_BLOCK_ERROR);
    EXPECT_EQ(result.block_number, 1u);
}

TEST(ReplayFromBlockDb_Eth, decode_block_error)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeErrorDecodeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_eth_error_decode_t replay_eth;

    auto result = replay_eth.run<
        eth_start_fork,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeReceiptFiberData,
        fakeInterpreter,
        empty_list_t>(state, state_trie, block_db, receipt_collector, 1u);

    EXPECT_EQ(
        result.status, replay_eth_error_decode_t::Status::DECODE_BLOCK_ERROR);
    EXPECT_EQ(result.block_number, 1u);
}

TEST(ReplayFromBlockDb_Eth, one_block)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_eth_t replay_eth;

    block_db._last_block_number = 1'000u;

    auto result = replay_eth.run<
        eth_start_fork,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeReceiptFiberData,
        fakeInterpreter,
        empty_list_t>(
        state, state_trie, block_db, receipt_collector, 100u, 101u);

    EXPECT_EQ(result.status, replay_eth_t::Status::SUCCESS);
    EXPECT_EQ(result.block_number, 100u);
    EXPECT_EQ(receipt_collector.size(), 1u);
}

TEST(ReplayFromBlockDb_Eth, frontier_run_from_zero)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_eth_t replay_eth;

    block_db._last_block_number = 1'234u;

    auto result = replay_eth.run<
        eth_start_fork,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeReceiptFiberData,
        fakeInterpreter,
        empty_list_t>(state, state_trie, block_db, receipt_collector, 0u);

    EXPECT_EQ(result.status, replay_eth_t::Status::SUCCESS_END_OF_DB);
    EXPECT_EQ(result.block_number, 1'234u);
    EXPECT_EQ(receipt_collector.size(), 1'235u);

    for (auto i = 0u; i < 1'235u; ++i) {
        EXPECT_EQ(
            receipt_collector[i][0].status,
            fork_traits::frontier::last_block_number);
    }
}

TEST(ReplayFromBlockDb_Eth, frontier_to_homestead)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_eth_t replay_eth;

    block_db._last_block_number = std::numeric_limits<uint64_t>::max();

    auto result = replay_eth.run<
        eth_start_fork,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeReceiptFiberData,
        fakeInterpreter,
        empty_list_t>(
        state,
        state_trie,
        block_db,
        receipt_collector,
        fork_traits::frontier::last_block_number - 10u,
        fork_traits::frontier::last_block_number + 10u);

    EXPECT_EQ(result.status, replay_eth_t::Status::SUCCESS);
    EXPECT_EQ(result.block_number, 1'150'008u);
    EXPECT_EQ(receipt_collector.size(), 20u);

    for (auto i = 0u; i < 11u; ++i) {
        EXPECT_EQ(
            receipt_collector[i][0].status,
            fork_traits::frontier::last_block_number);
    }
    for (auto i = 11u; i < receipt_collector.size(); ++i) {
        EXPECT_EQ(
            receipt_collector[i][0].status,
            fork_traits::homestead::last_block_number);
    }
}

TEST(ReplayFromBlockDb_Eth, berlin_to_london)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_eth_t replay_eth;

    block_db._last_block_number = std::numeric_limits<uint64_t>::max();

    auto result = replay_eth.run<
        eth_start_fork,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeReceiptFiberData,
        fakeInterpreter,
        empty_list_t>(
        state,
        state_trie,
        block_db,
        receipt_collector,
        fork_traits::berlin::last_block_number - 10u,
        fork_traits::berlin::last_block_number + 10u);

    EXPECT_EQ(result.status, replay_eth_t::Status::SUCCESS);
    EXPECT_EQ(result.block_number, 12'965'008u);
    EXPECT_EQ(receipt_collector.size(), 20u);

    for (auto i = 0u; i < 11u; ++i) {
        EXPECT_EQ(
            receipt_collector[i][0].status,
            fork_traits::berlin::last_block_number);
    }
    for (auto i = 11u; i < receipt_collector.size(); ++i) {
        EXPECT_EQ(
            receipt_collector[i][0].status,
            fork_traits::london::last_block_number);
    }
}

TEST(ReplayFromBlockDb_Eth, frontier_to_spurious_dragon)
{
    state_t state;
    fakeEmptyStateTrie<state_t> state_trie;
    fakeBlockDb block_db;
    receipt_collector_t receipt_collector;
    replay_eth_t replay_eth;

    block_db._last_block_number = std::numeric_limits<uint64_t>::max();

    auto result = replay_eth.run<
        eth_start_fork,
        fakeEmptyTP,
        fakeEmptyEvm,
        StaticPrecompiles,
        fakeEmptyEvmHost,
        fakeReceiptFiberData,
        fakeInterpreter,
        empty_list_t>(
        state,
        state_trie,
        block_db,
        receipt_collector,
        fork_traits::frontier::last_block_number - 10u,
        fork_traits::homestead::last_block_number + 10u);

    EXPECT_EQ(result.status, replay_eth_t::Status::SUCCESS);
    EXPECT_EQ(result.block_number, 2'675'008u);
    EXPECT_EQ(receipt_collector.size(), 1'525'020u);

    for (auto i = 0u; i < 11u; ++i) {
        EXPECT_EQ(
            receipt_collector[i][0].status,
            fork_traits::frontier::last_block_number);
    }
    for (auto i = 11u; i < receipt_collector.size() - 9u; ++i) {
        EXPECT_EQ(
            receipt_collector[i][0].status,
            fork_traits::homestead::last_block_number);
    }
    for (auto i = receipt_collector.size() - 9u; i < receipt_collector.size();
         ++i) {
        EXPECT_EQ(
            receipt_collector[i][0].status,
            fork_traits::spurious_dragon::last_block_number);
    }
}
