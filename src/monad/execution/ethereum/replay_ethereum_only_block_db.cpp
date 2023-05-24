#include <monad/config.hpp>

#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>

#include <monad/execution/block_processor.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/replay_block_db.hpp>
#include <monad/execution/static_precompiles.hpp>

#include <monad/execution/stats/stats.hpp>

#include <monad/execution/test/fakes.hpp>

#include <CLI/CLI.hpp>
#include <filesystem>
#include <fstream>
#include <ostream>

MONAD_NAMESPACE_BEGIN

using fakeState = execution::fake::State;
using receiptCollector =
    std::vector<std::vector<Receipt>>; // this is technically not a fake, thus
                                       // the name
using statsCollector = std::vector<execution::stats::BlockStats>;
using eth_start_fork = fork_traits::frontier;

template <class TTraits, class TState, class TEvm, class TStaticPrecompiles>
struct fakeEvmHost
{
    evmc_result _result{};
    Receipt _receipt{};

    [[nodiscard]] static constexpr inline evmc_message
    make_msg_from_txn(Transaction const &)
    {
        return {.kind = EVMC_CALL};
    }

    [[nodiscard]] constexpr inline Receipt make_receipt_from_result(
        evmc::Result const &, Transaction const &, uint64_t const)
    {
        return _receipt;
    }

    [[nodiscard]] inline evmc::Result call(evmc_message const &) noexcept
    {
        return evmc::Result{_result};
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

template <class TState, concepts::fork_traits<TState> TTraits>
struct fakeEmptyEvm
{
};

template <class TTraits, class TState, class TEvm, class TStaticPrecompiles>
struct fakeEmptyEvmHost
{
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

template <class TExecution>
class fakeEmptyBP
{
public:
    template <class TState, class TFiberData, class TStatsCollector>
    std::vector<Receipt> execute(TState &, Block &, TStatsCollector &)
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

MONAD_NAMESPACE_END

int main(int argc, char *argv[])
{
    CLI::App cli{"replay_ethereum"};

    std::filesystem::path block_db_path{};
    std::string output_file;
    std::ofstream ofile;
    monad::block_num_t start_block_number;
    monad::block_num_t finish_block_number;

    cli.add_option("-b, --block-db", block_db_path, "block_db directory")
        ->required();
    auto output_file_opt =
        cli.add_option("-o, --output", output_file, "output file name");
    cli.add_option("-s, --start", start_block_number, "start block numer")
        ->required();
    auto finish_block_number_opt = cli.add_option(
        "-f, --finish", finish_block_number, "1 pass the last executed block");
    cli.parse(argc, argv);

    monad::db::BlockDb block_db(block_db_path);
    monad::receiptCollector receipt_collector;
    monad::statsCollector stats_collector;
    monad::fakeState fake_state;
    monad::fakeEmptyStateTrie<monad::fakeState> fake_state_trie;

    if (*output_file_opt) {
        ofile.open(output_file);
    }
    std::ostream &output = (*output_file_opt) ? ofile : std::cout;

    monad::execution::ReplayFromBlockDb<
        monad::fakeState,
        monad::db::BlockDb,
        monad::execution::BoostFiberExecution,
        monad::fakeEmptyBP,
        monad::fakeEmptyStateTrie,
        monad::fakeEmptyTransactionTrie,
        monad::fakeEmptyReceiptTrie,
        monad::receiptCollector,
        monad::statsCollector>
        replay_eth;

    if (*finish_block_number_opt) {
        [[maybe_unused]] auto result = replay_eth.run<
            monad::eth_start_fork,
            monad::fakeEmptyTP,
            monad::fakeEmptyEvm,
            monad::execution::StaticPrecompiles,
            monad::fakeEmptyEvmHost,
            monad::fakeEmptyFiberData>(
            fake_state,
            fake_state_trie,
            block_db,
            receipt_collector,
            stats_collector,
            output,
            start_block_number,
            finish_block_number);
    }
    else {
        [[maybe_unused]] auto result = replay_eth.run<
            monad::eth_start_fork,
            monad::fakeEmptyTP,
            monad::fakeEmptyEvm,
            monad::execution::StaticPrecompiles,
            monad::fakeEmptyEvmHost,
            monad::fakeEmptyFiberData>(
            fake_state,
            fake_state_trie,
            block_db,
            receipt_collector,
            stats_collector,
            output,
            start_block_number);
    }

    return 0;
}