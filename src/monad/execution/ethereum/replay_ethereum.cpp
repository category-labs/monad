#include <monad/config.hpp>

#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>

#include <monad/execution/block_processor.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/replay_block_db.hpp>
#include <monad/execution/static_precompiles.hpp>
#include <monad/execution/test/fakes.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/execution/transaction_processor_data.hpp>

#include <monad/execution/test/fakes.hpp>

#include <monad/logging/monad_log.hpp>

#include <CLI/CLI.hpp>

#include <filesystem>

MONAD_NAMESPACE_BEGIN

using fakeState = execution::fake::State;
using receiptCollector = std::vector<std::vector<Receipt>>;
using eth_start_fork = fork_traits::frontier;

struct fakeInterpreter
{
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
    CLI::App cli{"replay_ethereum_block_db"};

    std::filesystem::path block_db_path{};
    monad::block_num_t start_block_number;
    std::optional<monad::block_num_t> finish_block_number = std::nullopt;

    monad::log::logger_t::start();

    // create all the loggers needed for the program
    auto *main_logger = monad::log::logger_t::create_logger("main_logger");
    [[maybe_unused]] auto *block_logger =
        monad::log::logger_t::create_logger("block_logger");
    [[maybe_unused]] auto *txn_logger =
        monad::log::logger_t::create_logger("txn_logger");
    [[maybe_unused]] auto *state_logger =
        monad::log::logger_t::create_logger("state_logger");

    auto main_log_level = monad::log::level_t::Info;
    auto block_log_level = monad::log::level_t::Info;
    auto txn_log_level = monad::log::level_t::Info;
    auto state_log_level = monad::log::level_t::Info;

    cli.add_option("-b, --block_db", block_db_path, "block_db directory")
        ->required();
    cli.add_option("-s, --start", start_block_number, "start block numer")
        ->required();
    cli.add_option(
        "-f, --finish", finish_block_number, "1 pass the last executed block");

    auto *log_levels = cli.add_subcommand("log_levels", "level of logging");
    log_levels->add_option("--main", main_log_level, "Log level for main");
    log_levels->add_option("--block", block_log_level, "Log level for block");
    log_levels->add_option("--txn", txn_log_level, "Log level for transaction");
    log_levels->add_option("--state", state_log_level, "Log level for state");

    cli.parse(argc, argv);

    using block_db_t = monad::db::BlockDb;
    using receipt_collector_t = monad::receiptCollector;
    using state_t = monad::fakeState;
    using execution_t = monad::execution::BoostFiberExecution;
    using transaction_trie_t = monad::fakeEmptyTransactionTrie;
    using receipt_trie_t = monad::fakeEmptyReceiptTrie;

    monad::log::logger_t::set_log_level("main_logger", main_log_level);
    monad::log::logger_t::set_log_level("block_logger", block_log_level);
    monad::log::logger_t::set_log_level("txn_logger", txn_log_level);
    monad::log::logger_t::set_log_level("state_logger", state_log_level);

    MONAD_LOG_INFO(
        main_logger,
        "Running with block_db = {}, start block number = {}, finish block "
        "number = {}",
        block_db_path,
        start_block_number,
        finish_block_number);

    block_db_t block_db(block_db_path);
    receipt_collector_t receipt_collector;
    state_t state;

    // In order to finish execution, this must be set to true
    state._merge_status = monad::fakeState::MergeStatus::WILL_SUCCEED;

    monad::execution::ReplayFromBlockDb<
        state_t,
        block_db_t,
        execution_t,
        monad::execution::AllTxnBlockProcessor,
        transaction_trie_t,
        receipt_trie_t,
        receipt_collector_t>
        replay_eth;

    [[maybe_unused]] auto result = replay_eth.run<
        monad::eth_start_fork,
        monad::execution::TransactionProcessor,
        monad::execution::fake::Evm,
        monad::execution::StaticPrecompiles,
        monad::execution::fake::EvmHost,
        monad::execution::TransactionProcessorFiberData,
        monad::fakeInterpreter,
        monad::eth_start_fork::static_precompiles_t>(
        state,
        block_db,
        receipt_collector,
        start_block_number,
        finish_block_number);

    MONAD_LOG_INFO(
        main_logger,
        "Finish running, status = {},  block number = {}, number of blocks run "
        "= {}",
        static_cast<int>(result.status),
        result.block_number,
        result.block_number - start_block_number + 1);

    return 0;
}
