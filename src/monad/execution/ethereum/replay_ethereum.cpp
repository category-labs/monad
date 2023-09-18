#include <monad/config.hpp>

#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>

#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/rocks_trie_db.hpp>

#include <monad/execution/block_processor.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/evmone_baseline_interpreter.hpp>

#include <monad/execution/precompiles.hpp>
#include <monad/execution/replay_block_db.hpp>
#include <monad/execution/test/fakes.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/execution/transaction_processor_data.hpp>

#include <monad/execution/test/fakes.hpp>

#include <monad/state/account_state.hpp>
#include <monad/state/code_state.hpp>
#include <monad/state/state.hpp>
#include <monad/state/value_state.hpp>

#include <monad/logging/formatter.hpp>

#include <CLI/CLI.hpp>
#include <quill/Quill.h>

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
    CLI::App cli{"replay_ethereum"};

    std::filesystem::path block_db_path{};
    std::filesystem::path state_db_path{};
    std::filesystem::path genesis_file_path{};
    uint64_t block_history_size = 1u;
    std::optional<monad::block_num_t> finish_block_number = std::nullopt;

    quill::start(true);

    auto log_level = quill::LogLevel::Info;

    cli.add_option("-b, --block_db", block_db_path, "block_db directory")
        ->required();
    cli.add_option("--state_db", state_db_path, "state_db directory")
        ->required();
    auto *has_genesis_file = cli.add_option(
        "--genesis_file", genesis_file_path, "genesis file directory");
    cli.add_option(
        "--block_history_size",
        block_history_size,
        "size of state_db block history");
    cli.add_option(
        "-f, --finish", finish_block_number, "1 pass the last executed block");
    cli.add_option("--log_level", log_level, "level of logging");

    cli.parse(argc, argv);

    auto const start_time = std::chrono::steady_clock::now();

    // Real Objects
    using db_t = monad::db::RocksTrieDB;
    using block_db_t = monad::db::BlockDb;
    using receipt_collector_t = monad::receiptCollector;
    using state_t = monad::state::State<
        monad::state::AccountState<db_t>,
        monad::state::ValueState<db_t>,
        monad::state::CodeState<db_t>,
        monad::db::BlockDb,
        db_t>;
    using execution_t = monad::execution::BoostFiberExecution;

    // Fakes
    using transaction_trie_t = monad::fakeEmptyTransactionTrie;
    using receipt_trie_t = monad::fakeEmptyReceiptTrie;

    quill::get_root_logger()->set_log_level(log_level);

    block_db_t block_db(block_db_path);
    db_t db{
        monad::db::Writable{}, state_db_path, std::nullopt, block_history_size};
    monad::state::AccountState accounts{db};
    monad::state::ValueState values{db};
    monad::state::CodeState code{db};
    state_t state{accounts, values, code, block_db, db};

    monad::block_num_t start_block_number = db.starting_block_number;

    LOG_INFO(
        "Running with block_db = {}, state_db = {}, block_history_size = {}, "
        "(inferred) start_block_number = {}, finish block number = {}",
        block_db_path,
        state_db_path,
        block_history_size,
        start_block_number,
        finish_block_number);

    if (start_block_number == 0) {
        MONAD_DEBUG_ASSERT(*has_genesis_file);
        read_and_verify_genesis(block_db, db, genesis_file_path);
        start_block_number = 1u;
    }

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
        monad::execution::EvmcHost,
        monad::execution::TransactionProcessorFiberData,
        monad::execution::EVMOneBaselineInterpreter<
            state_t::ChangeSet,
            monad::eth_start_fork>>(
        state,
        block_db,
        receipt_collector,
        start_block_number,
        finish_block_number);

    auto const finished_time = std::chrono::steady_clock::now();
    auto const elapsed_ms =
        std::chrono::duration_cast<std::chrono::milliseconds>(
            finished_time - start_time);

    LOG_INFO(
        "Finish running, status = {}, finish(stopped) block number = {}, "
        "number of blocks run = {}, time_elapsed = {}",
        static_cast<int>(result.status),
        result.block_number,
        result.block_number - start_block_number + 1,
        elapsed_ms);

    return 0;
}
