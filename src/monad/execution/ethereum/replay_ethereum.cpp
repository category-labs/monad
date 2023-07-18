#include <monad/config.hpp>

#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>

#include <monad/db/in_memory_db.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/rocks_db.hpp>
#include <monad/db/rocks_trie_db.hpp>

#include <monad/execution/block_processor.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/evmone_baseline_interpreter.hpp>

#include <monad/execution/replay_block_db.hpp>
#include <monad/execution/static_precompiles.hpp>
#include <monad/execution/test/fakes.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/execution/transaction_processor_data.hpp>

#include <monad/execution/test/fakes.hpp>

#include <monad/logging/monad_log.hpp>

#include <monad/state/account_state.hpp>
#include <monad/state/code_state.hpp>
#include <monad/state/state.hpp>
#include <monad/state/value_state.hpp>

#include <CLI/CLI.hpp>

#include <filesystem>

MONAD_NAMESPACE_BEGIN

using receiptCollector = std::vector<std::vector<Receipt>>;
using eth_start_fork = fork_traits::frontier;

class fakeEmptyTransactionTrie
{
public:
    fakeEmptyTransactionTrie(std::vector<Transaction> const &) {}
    bytes32_t root_hash() const { return NULL_ROOT; }
};

class fakeEmptyReceiptTrie
{
public:
    fakeEmptyReceiptTrie(std::vector<Receipt> const &) {}
    bytes32_t root_hash() const { return NULL_ROOT; }
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
    [[maybe_unused]] auto *trie_db_logger =
        monad::log::logger_t::create_logger("trie_db_logger");

    auto main_log_level = monad::log::level_t::Info;
    auto block_log_level = monad::log::level_t::Info;
    auto txn_log_level = monad::log::level_t::Info;
    auto state_log_level = monad::log::level_t::Info;
    auto trie_db_log_level = monad::log::level_t::Info;

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
    log_levels->add_option(
        "--trie_db", trie_db_log_level, "Log level for trie_db");

    cli.parse(argc, argv);

    // Real Objects
    using code_db_t = std::unordered_map<monad::address_t, monad::byte_string>;
    using db_t = monad::db::InMemoryTrieDB;
    using block_db_t = monad::db::BlockDb;
    using receipt_collector_t = monad::receiptCollector;
    using state_t = monad::state::State<
        monad::state::AccountState<db_t>,
        monad::state::ValueState<db_t>,
        monad::state::CodeState<code_db_t>,
        monad::db::BlockDb,
        db_t>;
    using execution_t = monad::execution::BoostFiberExecution;

    // Fakes
    using transaction_trie_t = monad::fakeEmptyTransactionTrie;
    using receipt_trie_t = monad::fakeEmptyReceiptTrie;

    monad::log::logger_t::set_log_level("main_logger", main_log_level);
    monad::log::logger_t::set_log_level("block_logger", block_log_level);
    monad::log::logger_t::set_log_level("txn_logger", txn_log_level);
    monad::log::logger_t::set_log_level("state_logger", state_log_level);
    monad::log::logger_t::set_log_level("trie_db_logger", trie_db_log_level);

    MONAD_LOG_INFO(
        main_logger,
        "Running with block_db = {}, start block number = {}, finish block "
        "number = {}",
        block_db_path,
        start_block_number,
        finish_block_number);

    block_db_t block_db(block_db_path);
    db_t db{};
    code_db_t code_db{};
    monad::state::AccountState accounts{db};
    monad::state::ValueState values{db};
    monad::state::CodeState code{code_db};
    state_t state{accounts, values, code, block_db, db};

    receipt_collector_t receipt_collector;

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
        monad::execution::Evm,
        monad::execution::StaticPrecompiles,
        monad::execution::EvmcHost,
        monad::execution::TransactionProcessorFiberData,
        monad::execution::EVMOneBaselineInterpreter<
            state_t::WorkingCopy,
            monad::eth_start_fork>,
        monad::eth_start_fork::static_precompiles_t>(
        state,
        block_db,
        receipt_collector,
        start_block_number,
        finish_block_number);

    MONAD_LOG_INFO(
        main_logger,
        "Finish running, status = {}, finish(stopped) block number = {}, "
        "number of blocks run "
        "= {}",
        static_cast<int>(result.status),
        result.block_number,
        result.block_number - start_block_number + 1);

    return 0;
}
