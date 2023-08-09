// #include "from_json.hpp"
#include <CLI/CLI.hpp>
#include <gtest/gtest.h>
// #include <boost/algorithm/string.hpp>
// #include <boost/core/demangle.hpp>
// #include <boost/mp11.hpp>
// #include <evmc/evmc.hpp>
// #include <format>
// #include <iostream>
// #include <monad/core/account.hpp>
// #include <monad/db/in_memory_trie_db.hpp>
// #include <monad/execution/ethereum/fork_traits.hpp>
// #include <monad/execution/ethereum/genesis.hpp>
// #include <monad/execution/evm.hpp>
// #include <monad/execution/evmc_host.hpp>
// #include <monad/execution/evmone_baseline_interpreter.hpp>
// #include <monad/execution/instruction_tracer.hpp>
// #include <monad/execution/static_precompiles.hpp>
// #include <monad/execution/test/fakes.hpp>
// #include <monad/execution/transaction_processor.hpp>
// #include <nlohmann/json.hpp>
// #include <ranges>
// #include <string>
// #include <tl/expected.hpp>
// #include <unordered_map>
// #include <variant>
//
// #include <monad/state/account_state.hpp>
// #include <monad/state/code_state.hpp>
// #include <monad/state/state.hpp>
// #include <monad/state/value_state.hpp>
//
namespace fs = std::filesystem;
//
// struct FileDoesNotExist
//{
//};
//
// struct JSONParseError
//{
//};
//
// using Error = std::variant<FileDoesNotExist, JSONParseError>;
//
// std::string read_file(fs::path const &file_path)
//{
//    if (!fs::exists(file_path)) {
//        throw std::runtime_error(fmt::format("{} does not exist", file_path));
//    }
//    std::ifstream file{file_path};
//    std::stringstream buffer;
//    buffer << file.rdbuf();
//    return buffer.str();
//}
//
// void write_file(fs::path const &file_path, std::string const &contents)
//{
//    std::ofstream file{file_path};
//    file << contents;
//}
//
// std::optional<size_t> to_fork_index(std::string_view s)
//{
//    std::string copy{s.data(), s.size()};
//    std::transform(s.begin(), s.end(), copy.begin(), [](auto c) {
//        return std::tolower(c);
//    });
//    if (s == "frontier") {
//        return 0;
//    }
//    if (s == "homestead") {
//        return 1;
//    }
//    if (s == "spurious_dragon") {
//        return 2;
//    }
//    if (s == "byzantium") {
//        return 3;
//    }
//    if (s == "constantinople") {
//        return 4;
//    }
//    if (s == "istanbul") {
//        return 5;
//    }
//    if (s == "berlin") {
//        return 6;
//    }
//    if (s == "london") {
//        return 7;
//    }
//    return std::nullopt;
//}
//
// using account_store_db_t = monad::db::InMemoryTrieDB;
// using code_db_t = std::unordered_map<monad::bytes32_t, monad::byte_string>;
// using state_t = monad::state::State<
//    monad::state::AccountState<account_store_db_t>,
//    monad::state::ValueState<account_store_db_t>,
//    monad::state::CodeState<code_db_t>, monad::db::BlockDb,
//    account_store_db_t>;
// using working_state_t =
// decltype(std::declval<state_t>().get_new_changeset(0u));
//
// template <typename TFork>
// using interpreter_t =
//    monad::execution::EVMOneBaselineInterpreter<working_state_t, TFork>;
//
// template <typename TFork>
// using transaction_processor_t =
//    monad::execution::TransactionProcessor<working_state_t, TFork>;
//
// template <typename TFork>
// using static_precompiles_t = monad::execution::StaticPrecompiles<
//    working_state_t, TFork, typename TFork::static_precompiles_t>;
//
// template <typename TFork>
// using evm_t = monad::execution::Evm<
//    working_state_t, TFork, static_precompiles_t<TFork>,
//    interpreter_t<TFork>>;
//
// template <typename TFork>
// using host_t = monad::execution::EvmcHost<working_state_t, TFork,
// evm_t<TFork>>;
//
// using namespace boost::mp11;
// using namespace monad::fork_traits;
//
// template <typename T>
// constexpr auto Traverse()
//{
//    if constexpr (requires { typename T::next_fork_t; }) {
//        return boost::mp11::
//            mp_push_front<decltype(Traverse<typename T::next_fork_t>()), T>{};
//    }
//    else {
//        return boost::mp11::mp_list<T>{};
//    }
//}
//
// template <>
// constexpr auto Traverse<no_next_fork_t>()
//{
//    return boost::mp11::mp_list<no_next_fork_t>{};
//}
//
// using all_forks_t = decltype(Traverse<monad::fork_traits::frontier>());
// static_assert(mp_size<all_forks_t>::value == 8);
//
// template <typename TFork>
// struct Execution
//{
//    Execution(
//        monad::BlockHeader const &block_header,
//        monad::Transaction const &transaction, working_state_t &state)
//        : host_{block_header, transaction, state}
//        , transaction_processor_{}
//    {
//    }
//
//    monad::Receipt
//    execute(working_state_t &state, monad::Transaction const &transaction)
//    {
//        using Status = typename transaction_processor_t<TFork>::Status;
//        typename decltype(transaction_processor_)::Status status =
//            transaction_processor_.validate(
//                state,
//                transaction,
//                host_.block_header_.base_fee_per_gas.value_or(0));
//        if (status != Status::SUCCESS) {
//            //            throw std::runtime_error("properly handle invalid
//            //            transactions");
//        }
//        return transaction_processor_.execute(
//            state,
//            host_,
//            transaction,
//            host_.block_header_.base_fee_per_gas.value_or(0));
//    }
//
//    host_t<TFork> host_;
//    transaction_processor_t<TFork> transaction_processor_;
//};
//
//// creates a sum type over all the forks:
//// std::variant<std::monostate, Execution<frontier>, Execution<homestead>,
///...>
// using execution_variant =
//     decltype([]<typename... Types>(boost::mp11::mp_list<Types...>) {
//         return std::variant<std::monostate, Types...>{};
//     }(mp_transform<Execution, all_forks_t>{}));
//
///**
// * execute a transaction with a given state using a fork specified at runtime
// * @param fork_index
// * @param state
// * @param transaction
// * @return a receipt of the transaction
// */
// monad::Receipt execute(
//    size_t fork_index, monad::BlockHeader const &block_header,
//    working_state_t &state, monad::Transaction const &transaction)
//{
//    // makes a glorified jump table by creating an array where the i'th index
//    // corresponds to an instance of the Execution struct with the i'th fork
//    // injected.
//    auto execution_array = []<typename... Ts>(
//                               mp_list<Ts...>,
//                               monad::BlockHeader const &block_header,
//                               working_state_t &state,
//                               monad::Transaction const &transaction) {
//        return std::array<execution_variant, sizeof...(Ts)>{
//            Execution<Ts>{block_header, transaction, state}...};
//    }(all_forks_t{}, block_header, state, transaction);
//
//    // we then dispatch into the appropriate fork at runtime using std::get
//    auto &variant = execution_array.at(fork_index);
//
//    std::optional<monad::Receipt> maybe_receipt;
//    mp_for_each<mp_iota_c<mp_size<all_forks_t>::value>>([&](auto I) {
//        if (I == fork_index) {
//            maybe_receipt =
//                std::get<Execution<mp_at_c<all_forks_t, I>>>(variant).execute(
//                    state, transaction);
//        }
//    });
//
//    return maybe_receipt.value();
//}
//
/**
 * @param path
 * @return if `path` is a directory, return a list of paths that is a result
 of
 * recursively walking the directory, or a list with the single path if `path`
 * is a file.
 */
std::vector<fs::path> walk(fs::path const &path)
{
    if (is_directory(path)) {
        std::vector<fs::path> res;
        for (auto const &p : fs::recursive_directory_iterator(path)) {
            res.push_back(p);
        }
        return res;
    }
    return {path};
}
//
// int main0(int argc, char **argv)
//{
//    [[maybe_unused]] auto *compatibility_logger =
//        monad::log::logger_t::create_logger("compatibility_logger");
//    [[maybe_unused]] auto *trie_db_logger =
//        monad::log::logger_t::create_logger("trie_db_logger");
//    trie_db_logger->set_log_level(quill::LogLevel::Debug);
//    [[maybe_unused]] auto *change_set_logger =
//        monad::log::logger_t::create_logger("change_set_logger");
//    change_set_logger->set_log_level(quill::LogLevel::Debug);
//    [[maybe_unused]] auto *evmone_baseline_interpreter_logger =
//        monad::log::logger_t::create_logger(
//            "evmone_baseline_interpreter_logger");
//    evmone_baseline_interpreter_logger->set_log_level(quill::LogLevel::Debug);
//
//    monad::log::logger_t::start();
//
//    MONAD_LOG_INFO(
//        compatibility_logger,
//        "running from working directory {}",
//        fs::current_path());
//
//    CLI::App cli{"compatibility"};
//
//    std::string fork_name;
//    cli.add_option(
//           "--state.fork", fork_name, "name of the ethereum fork to run on")
//        ->required()
//        ->check([](auto const &fork_name) -> std::string {
//            auto const index = to_fork_index(fork_name);
//            if (index.has_value()) {
//                return "";
//            }
//            else {
//                return std::format(
//                    "invalid fork name \"{}\", must be one of: {}",
//                    fork_name,
//                    []() {
//                        std::vector<std::string> fork_names;
//                        mp_for_each<all_forks_t>([&](auto fork) {
//                            std::vector<std::string> tokens;
//                            auto const demangled_name =
//                                boost::core::demangle(typeid(fork).name());
//                            boost::algorithm::split(
//                                tokens, demangled_name,
//                                boost::is_any_of("::"));
//                            if (!tokens.empty()) {
//                                fork_names.push_back(tokens.back());
//                            }
//                        });
//                        return boost::algorithm::join(fork_names, ", ");
//                    }());
//            }
//        });
//
//    fs::path input_alloc;
//    cli.add_option("--input.alloc", input_alloc, "pre state")->required();
//
//    fs::path input_env;
//    cli.add_option(
//           "--input.env",
//           input_env,
//           "JSON file containing an object with the prestate")
//        ->required();
//
//    fs::path input_transactions;
//    cli.add_option(
//           "--input.txs",
//           input_transactions,
//           "JSON file containing list of transactions to execute")
//        ->required();
//
//    fs::path output_directory;
//    cli.add_option(
//           "--output.directory",
//           output_directory,
//           "directory to dump output state and transaction trace")
//        ->required();
//
//    cli.parse(argc, argv);
//
//    if (fs::exists(output_directory)) {
//        if (!fs::is_directory(output_directory)) {
//            throw std::runtime_error(fmt::format(
//                "The value passed into --output.directory ({}) is a file that
//                " "already exists and must be a directory. Remove it and try "
//                "again.",
//                fs::absolute(output_directory)));
//        }
//    }
//    else {
//        fs::create_directory(output_directory);
//    }
//
//    auto const fork_index = to_fork_index(fork_name).value();
//
//    {
//        auto const input_alloc_contents =
//            nlohmann::json::parse(read_file(input_alloc));
//
//        auto const input_env_contents =
//            nlohmann::json::parse(read_file(input_env));
//
//        auto const input_transactions_contents =
//            nlohmann::json::parse(read_file(input_transactions));
//
//        monad::db::BlockDb blocks{"some_path"};
//        account_store_db_t db{};
//        monad::state::AccountState accounts{db};
//        monad::state::ValueState values{db};
//        code_db_t code_db{};
//        monad::state::CodeState codes{code_db};
//        monad::state::State s{accounts, values, codes, blocks, db};
//        MONAD_LOG_INFO(
//            compatibility_logger,
//            "root hash before transactions: {}",
//            evmc::hex(db.root_hash()));
//        quill::flush();
//
//        auto working_state = s.get_new_changeset(0u);
//
//        auto block_header =
//            ::test::beneficiary_from_json(working_state, input_env_contents);
//        test::from_json(working_state, input_alloc_contents);
//
//        auto const transaction = ::test::from_json<monad::Transaction>(
//            input_transactions_contents[0]);
//
//        size_t transaction_index = 0;
//        uint64_t total_gas_used = 0;
//        {
//            MONAD_LOG_INFO(
//                compatibility_logger,
//                "execution transaction {}",
//                transaction_index);
//            auto receipt =
//                execute(fork_index, block_header, working_state, transaction);
//
//            MONAD_LOG_INFO(
//                compatibility_logger,
//                "gas used during transaction {} = {}",
//                transaction_index,
//                intx::to_string(monad::uint256_t{receipt.gas_used}, 16));
//
//            total_gas_used += receipt.gas_used;
//
//            auto const rlp_encoded_transaction =
//                monad::rlp::encode_transaction(transaction);
//            auto const transaction_hash = ethash_keccak256(
//                rlp_encoded_transaction.data(),
//                rlp_encoded_transaction.size());
//            auto const transaction_hash_byte_string = monad::byte_string{
//                reinterpret_cast<uint8_t const *>(transaction_hash.bytes),
//                32};
//
//            auto const transaction_trace_file_name = fmt::format(
//                "trace-{}-{}.jsonl",
//                transaction_index,
//                test::hex0x(transaction_hash_byte_string));
//
//            write_file(
//                output_directory / transaction_trace_file_name,
//                monad::execution::InstructionTracer::get_trace());
//
//            MONAD_LOG_INFO(
//                compatibility_logger,
//                "instruction trace written to {}",
//                output_directory / transaction_trace_file_name);
//
//            assert(receipt.status);
//            transaction_index++;
//        }
//
//        MONAD_LOG_INFO(compatibility_logger, "merging and committing");
//        using namespace std::chrono_literals;
//        std::this_thread::sleep_for(5s);
//
//        std::vector<monad::address_t> changed_account_addresses;
//        std::transform(
//            working_state.accounts_.changed_.begin(),
//            working_state.accounts_.changed_.end(),
//            std::back_inserter(changed_account_addresses),
//            [](auto const &change) { return change.first; });
//        s.merge_changes(working_state);
//        s.apply_block_reward(
//            block_header.beneficiary,
//            monad::uint256_t{0} /* make block reward configurable */);
//        s.commit();
//        auto const post_hash = evmc::hex(db.root_hash());
//        MONAD_LOG_INFO(
//            compatibility_logger,
//            "root hash after transactions: {}",
//            post_hash);
//        MONAD_LOG_INFO(
//            compatibility_logger,
//            "account state hash after transactions: {}",
//            evmc::hex(s.get_state_hash()));
//        MONAD_LOG_INFO(
//            compatibility_logger,
//            "total gas used: {}",
//            intx::to_string(monad::uint256_t{total_gas_used}, 16));
//        auto const post_state = test::to_json(s, changed_account_addresses);
//
//        write_file(output_directory / "post.json", post_state.dump(2));
//        MONAD_LOG_INFO(
//            compatibility_logger,
//            "post state written to {}",
//            fs::absolute(output_directory / "post.json"));
//
//        quill::flush();
//    }
//    quill::remove_logger(trie_db_logger);
//    return 0;
//}

#include <monad/logging/monad_log.hpp>

class MyFixture : public ::testing::Test
{
public:
    // All of these optional, just like in regular macro usage.
    static void SetUpTestSuite() {}
    static void TearDownTestSuite() {}
    void SetUp() override {}
    void TearDown() override {}
};

class MyTest : public MyFixture
{
public:
    explicit MyTest(fs::path path)
        : path_{path}
    {
    }
    void TestBody() override { EXPECT_TRUE(false); }

private:
    fs::path path_;
};

int main(int argc, char **argv)
{
    [[maybe_unused]] auto *compatibility_logger =
        monad::log::logger_t::create_logger("compatibility_logger");
    [[maybe_unused]] auto *trie_db_logger =
        monad::log::logger_t::create_logger("trie_db_logger");
    trie_db_logger->set_log_level(quill::LogLevel::Debug);
    [[maybe_unused]] auto *change_set_logger =
        monad::log::logger_t::create_logger("change_set_logger");
    change_set_logger->set_log_level(quill::LogLevel::Debug);
    [[maybe_unused]] auto *evmone_baseline_interpreter_logger =
        monad::log::logger_t::create_logger(
            "evmone_baseline_interpreter_logger");
    evmone_baseline_interpreter_logger->set_log_level(quill::LogLevel::Debug);

    monad::log::logger_t::start();

    MONAD_LOG_INFO(
        compatibility_logger,
        "running from working directory {}",
        fs::current_path());

    testing::InitGoogleTest(&argc, argv);

    CLI::App cli{"compatibility"};

    fs::path ethereum_tests_path;
    cli.add_option(
           "--ethereum_tests",
           ethereum_tests_path,
           "path to the ethereum tests repo")
        ->required()
        ->check(CLI::ExistingDirectory);

    cli.parse(argc, argv);

    MONAD_LOG_INFO(quill::get_logger(), "directory {}", ethereum_tests_path);

    if (is_directory(ethereum_tests_path)) {
        std::vector<fs::path> files;
        for (auto const &p :
             fs::recursive_directory_iterator(ethereum_tests_path)) {
            if (p.is_regular_file() && p.path().extension() == ".json") {
                files.push_back(p);
            }
        }

        for (auto const &p : files) {
            auto const test_suite_name =
                fs::relative(p, ethereum_tests_path).parent_path().string();
            auto const test_name = p.stem();
            MONAD_LOG_INFO(
                quill::get_logger(),
                "file fs::relative({}, {}).parent_path().string() = {} {}",
                p.string(),
                ethereum_tests_path.string(),
                test_suite_name,
                p);

            testing::RegisterTest(
                test_suite_name.c_str(),
                test_name.string().c_str(),
                nullptr,
                nullptr,
                p.string().c_str(),
                0,
                [&p]() -> testing::Test * { return new MyTest(p); });
        }

        return RUN_ALL_TESTS();
    }
    return 0;
}
