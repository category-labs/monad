#include <monad/config.hpp>

#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>

#include <monad/execution/block_processor.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/replay_block_db.hpp>
#include <monad/execution/static_precompiles.hpp>
#include <monad/execution/test/fakes.hpp>

#include <monad/logging/monad_log.hpp>

#include <CLI/CLI.hpp>
#include <quill/Quill.h>

#include <filesystem>

MONAD_NAMESPACE_BEGIN

using fakeState = execution::fake::State;
using receiptCollector = std::vector<std::vector<Receipt>>;
using eth_start_fork = fork_traits::frontier;

template <class TTraits, class TState, class TEvm, class TStaticPrecompiles>
struct fakeEvmHost
{
    evmc_result _result{};
    Receipt _receipt{};

    [[nodiscard]] static constexpr inline evmc_message
    make_msg_from_txn(Transaction const &) noexcept
    {
        return {.kind = EVMC_CALL};
    }

    [[nodiscard]] constexpr inline Receipt make_receipt_from_result(
        evmc::Result const &, Transaction const &, uint64_t const) noexcept
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
        TState &, TEvmHost &, BlockHeader const &,
        Transaction const &) const noexcept
    {
        return {};
    }

    Status validate(TState const &, Transaction const &, uint64_t) noexcept
    {
        return Status::SUCCESS;
    }
};

template <
    class TState, concepts::fork_traits<TState> TTraits,
    class TStaticPrecompiles, class TInterpreter>
struct fakeEmptyEvm
{
};

template <class TTraits, class TState, class TEvm>
struct fakeEmptyEvmHost
{
};

struct fakeInterpreter
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
    Receipt get_receipt() noexcept { return _result; }
    inline void operator()() {}
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

MONAD_NAMESPACE_END

int main(int argc, char *argv[])
{
    CLI::App cli{"replay_ethereum_block_db"};

    std::filesystem::path block_db_path{};
    monad::block_num_t start_block_number;
    std::optional<monad::block_num_t> finish_block_number = std::nullopt;
    quill::LogLevel log_level = quill::LogLevel::Info;

    cli.add_option("-b, --block-db", block_db_path, "block_db directory")
        ->required();
    cli.add_option("-s, --start", start_block_number, "start block numer")
        ->required();
    cli.add_option(
        "-f, --finish", finish_block_number, "1 pass the last executed block");

    // Should support different log-level for different part of program later
    // on; for simplicity, now only supports 1 log level throughout the program
    cli.add_option("-l, --log-level", log_level, "level of logging");
    cli.parse(argc, argv);

    using block_db_t = monad::db::BlockDb;
    using receipt_collector_t = monad::receiptCollector;
    using state_t = monad::fakeState;
    using state_trie_t = monad::fakeEmptyStateTrie<state_t>;
    using execution_t = monad::execution::BoostFiberExecution;
    using transaction_trie_t = monad::fakeEmptyTransactionTrie;
    using receipt_trie_t = monad::fakeEmptyReceiptTrie;

    monad::log::logger_t::start();

    // create all the loggers needed for the program
    [[maybe_unused]] auto *main_logger =
        monad::log::logger_t::create_logger("main_logger");
    [[maybe_unused]] auto *block_logger =
        monad::log::logger_t::create_logger("block_logger");
    [[maybe_unused]] auto *txn_logger =
        monad::log::logger_t::create_logger("txn_logger");
    [[maybe_unused]] auto *state_logger =
        monad::log::logger_t::create_logger("state_logger");

    // set loggers logging level, there is only 1 log level for now
    // TODO: flexible log levels for different logger
    monad::log::logger_t::set_log_level("main_logger", log_level);
    monad::log::logger_t::set_log_level("block_logger", log_level);
    monad::log::logger_t::set_log_level("txn_logger", log_level);
    monad::log::logger_t::set_log_level("state_logger", log_level);

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
    state_trie_t state_trie;

    monad::execution::ReplayFromBlockDb<
        state_t,
        block_db_t,
        execution_t,
        monad::fakeEmptyBP,
        monad::fakeEmptyStateTrie,
        transaction_trie_t,
        receipt_trie_t,
        receipt_collector_t,
        monad::log::logger_t>
        replay_eth;

    [[maybe_unused]] auto result = replay_eth.run<
        monad::eth_start_fork,
        monad::fakeEmptyTP,
        monad::fakeEmptyEvm,
        monad::execution::StaticPrecompiles,
        monad::fakeEmptyEvmHost,
        monad::fakeEmptyFiberData,
        monad::fakeInterpreter,
        monad::eth_start_fork::static_precompiles_t>(
        state,
        state_trie,
        block_db,
        receipt_collector,
        start_block_number,
        finish_block_number);

    MONAD_LOG_INFO(
        main_logger,
        "Finished running, status = {},  block number = {}",
        static_cast<int>(result.status),
        result.block_number);

    return 0;
}
