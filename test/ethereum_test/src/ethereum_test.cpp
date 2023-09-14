#include <ethereum_test.hpp>
#include <monad/db/in_memory_trie_db.hpp>

#include <monad/logging/monad_log.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>
#include <monad/test/dump_state_from_db.hpp>

#include <test_resource_data.h>

#include <gtest/gtest.h>

#include <algorithm>
#include <iostream>
#include <shared_mutex>

MONAD_TEST_NAMESPACE_BEGIN

using mutex_t = std::shared_mutex;

using db_t = monad::db::InMemoryTrieDB;
using state_t = monad::state::State<mutex_t, monad::execution::fake::BlockDb>;

template <typename TFork>
using interpreter_t =
    monad::execution::EVMOneBaselineInterpreter<state_t, TFork>;

template <typename TFork>
using transaction_processor_t =
    monad::execution::TransactionProcessor<state_t, TFork>;

template <typename TFork>
using evm_t = monad::execution::Evm<state_t, TFork, interpreter_t<TFork>>;

template <typename TFork>
using host_t = monad::execution::EvmcHost<state_t, TFork, evm_t<TFork>>;

template <typename TFork>
struct Execution
{
    host_t<TFork> host;
    transaction_processor_t<TFork> transaction_processor;

    Execution(
        monad::BlockHeader const &block_header,
        monad::Transaction const &transaction, state_t &state)
        : host{block_header, transaction, state}
        , transaction_processor{}
    {
    }

    [[nodiscard]] std::optional<monad::Receipt>
    execute(state_t &state, monad::Transaction const &transaction)
    {
        auto const status = transaction_processor.validate(
            state,
            transaction,
            host.block_header_.base_fee_per_gas.value_or(0));
        if (status != transaction_processor_t<TFork>::Status::SUCCESS) {
            return std::nullopt;
        }
        return transaction_processor.execute(
            state,
            host,
            transaction,
            host.block_header_.base_fee_per_gas.value_or(0),
            host.block_header_.beneficiary);
    }
};

// creates a sum type over all the forks:
// variant<std::monostate, Execution<frontier>, Execution<homestead>, ...>
using execution_variant =
    decltype([]<typename... Types>(boost::mp11::mp_list<Types...>) {
        return std::variant<std::monostate, Types...>{};
    }(boost::mp11::mp_transform<Execution, monad::fork_traits::all_forks_t>{}));

/**
 * execute a transaction with a given state using a fork specified at
 * runtime
 * @param fork_index
 * @param state
 * @param transaction
 * @return a receipt of the transaction
 */
[[nodiscard]] std::optional<monad::Receipt> execute(
    size_t fork_index, monad::BlockHeader const &block_header, state_t &state,
    monad::Transaction const &transaction)
{
    using namespace boost::mp11;

    using namespace monad;
    // create a table of fork types
    auto execution_array = []<typename... Ts>(
                               mp_list<Ts...>,
                               BlockHeader const &block_header,
                               state_t &s,
                               Transaction const &transaction) {
        return std::array<execution_variant, sizeof...(Ts)>{
            Execution<Ts>{block_header, transaction, s}...};
    }(fork_traits::all_forks_t{}, block_header, state, transaction);

    // we then dispatch into the appropriate fork at runtime using std::get
    auto &variant = execution_array.at(fork_index);

    std::optional<monad::Receipt> maybe_receipt;
    mp_for_each<mp_iota_c<mp_size<fork_traits::all_forks_t>::value>>(
        [&](auto I) {
            if (I == fork_index) {
                using TTraits = mp_at_c<fork_traits::all_forks_t, I>;
                maybe_receipt = std::get<Execution<TTraits>>(variant).execute(
                    state, transaction);

                auto const gas_used = maybe_receipt.has_value()
                                          ? maybe_receipt.value().gas_used
                                          : 0;
                auto const gas_award = TTraits::calculate_txn_award(
                    transaction,
                    block_header.base_fee_per_gas.value_or(0),
                    gas_used);
                if (fork_index < fork_index_map.at("EIP158") ||
                    gas_award != 0) {
                    state.add_to_balance(block_header.beneficiary, gas_award);
                }
            }
        });

    return maybe_receipt;
}

void EthereumTests::register_test(
    std::string suite_name, std::filesystem::path const &file,
    std::optional<size_t> fork_index, std::optional<size_t> txn_index)
{
    // Normalize the test name so that gtest_filter can recognize it. ie.
    // --gtest_filter=stZeroKnowledge2.ecmul_0-3_5616_21000_128 will not work
    // because gtest interprets the minus sign as exclusion
    std::ranges::replace(suite_name, '-', '_');
    auto test_name = file.stem().string();
    std::ranges::replace(test_name, '-', '_');

    testing::RegisterTest(
        suite_name.c_str(),
        test_name.c_str(),
        nullptr,
        nullptr,
        file.string().c_str(),
        0,
        [file, suite_name, fork_index, txn_index]() -> testing::Test * {
            return new EthereumTests(
                file,
                suite_name,
                file.stem().string(),
                file.string(),
                fork_index,
                txn_index);
        });
}

void EthereumTests::register_test_files(
    std::filesystem::path const &root, std::optional<size_t> fork_index,
    std::optional<size_t> txn_index)
{
    for (auto const &directory_entry :
         std::filesystem::recursive_directory_iterator{root}) {
        if (directory_entry.is_regular_file() &&
            directory_entry.path().extension() == ".json") {
            register_test(
                std::filesystem::relative(directory_entry.path(), root)
                    .parent_path()
                    .string(),
                directory_entry.path(),
                fork_index,
                txn_index);
        }
    }
}

[[nodiscard]] std::optional<size_t> to_fork_index(std::string const &fork_name)
{
    // static assert here to remind anyone who adds a fork to update this
    // function
    static_assert(
        boost::mp11::mp_size<monad::fork_traits::all_forks_t>::value == 12);

    if (fork_index_map.contains(fork_name)) {
        return fork_index_map.at(fork_name);
    }
    return std::nullopt;
}

StateTransitionTest EthereumTests::load_state_test(
    nlohmann::json json, std::string suite_name, std::string test_name,
    std::string file_name, std::optional<size_t> fork_index,
    std::optional<size_t> txn_index)
{
    if (!json.is_object()) {
        throw std::invalid_argument{fmt::format(
            "Error parsing {} {} {}: expected a JSON object",
            suite_name,
            test_name,
            file_name)};
    }
    if (json.empty()) {
        throw std::invalid_argument{fmt::format(
            "Error parsing {} {} {}: expected a non-empty JSON object",
            suite_name,
            test_name,
            file_name)};
    }
    if (json.items().begin().key() != test_name) {
        throw std::invalid_argument{fmt::format(
            "Error parsing {} {} {}: expected root key of JSON object to "
            "match {}, "
            "but got {}",
            suite_name,
            test_name,
            file_name,
            test_name,
            json.items().begin().key())};
    }
    auto const &json_test = *json.begin();

    std::vector<Case> test_cases;
    for (auto const &[revision_name, expectations] :
         json_test.at("post").items()) {
        auto maybe_fork_index = to_fork_index(revision_name);
        if (!maybe_fork_index.has_value()) {
            MONAD_LOG_ERROR(
                quill::get_logger("ethereum_test_logger"),
                "skipping post state in {}:{}:{} due to invalid "
                "fork index {}",
                suite_name,
                test_name,
                file_name,
                revision_name);
            continue;
        }
        else if (fork_index.has_value() && maybe_fork_index != fork_index) {
            continue;
        }

        if (txn_index.has_value()) {
            if (txn_index.value() < expectations.size()) {
                test_cases.emplace_back(Case{
                    .fork_index = maybe_fork_index.value(),
                    .fork_name = revision_name,
                    .expectations = {expectations.at(txn_index.value())
                                         .get<Case::Expectation>()}});
            }
            continue;
        }

        test_cases.emplace_back(Case{
            .fork_index = maybe_fork_index.value(),
            .fork_name = revision_name,
            .expectations =
                expectations.get<std::vector<Case::Expectation>>()});
    }

    return {
        .shared_transaction_data =
            json_test.at("transaction").get<SharedTransactionData>(),
        .cases = std::move(test_cases)};
}

void EthereumTests::run_state_test(
    StateTransitionTest const &test, nlohmann::json const &json)
{
    auto *logger = quill::get_logger("ethereum_test_logger");
    for (auto const &[fork_index, fork_name, expectations] : test.cases) {
        for (size_t case_index = 0; case_index != expectations.size();
             ++case_index) {
            auto const &expected = expectations[case_index];
            monad::Transaction const transaction = [&] {
                auto const &shared_transaction_data =
                    test.shared_transaction_data;
                monad::Transaction::AccessList access_list;
                if (!shared_transaction_data.access_lists.empty()) {
                    access_list = shared_transaction_data.access_lists.at(
                        expected.indices.input);
                }
                return monad::Transaction{
                    .nonce = shared_transaction_data.nonce,
                    .gas_price = shared_transaction_data.gas_price,
                    .gas_limit = shared_transaction_data.gas_limits.at(
                        expected.indices.gas_limit),
                    .amount = shared_transaction_data.values.at(
                        expected.indices.value),
                    .to = shared_transaction_data.to,
                    .from = shared_transaction_data.sender,
                    .data = shared_transaction_data.inputs.at(
                        expected.indices.input),
                    .type = shared_transaction_data.transaction_type,
                    .access_list = std::move(access_list),
                    .priority_fee = shared_transaction_data.priority_fee};
            }();

            monad::execution::fake::BlockDb fake_block_db;

            db_t db{};

            monad::BlockState<mutex_t> bs;

            // every test json file is initially keyed with the test
            // name
            MONAD_ASSERT(json.is_object() && !json.empty());

            auto const &j_t = *json.begin();
            {
                monad::state::State state{bs, db, fake_block_db};

                MONAD_LOG_INFO(logger, "Starting to load state from json");

                load_state_from_json(j_t.at("pre"), state);
                merge(bs.state, state.state_);
                merge(bs.code, state.code_);
            }

            auto block_header = j_t.at("env").get<monad::BlockHeader>();

            MONAD_LOG_INFO(
                logger, "Starting to execute transaction {}", case_index);

            monad::state::State state{bs, db, fake_block_db};
            auto maybe_receipt =
                execute(fork_index, block_header, state, transaction);

            merge(bs.state, state.state_);
            merge(bs.code, state.code_);
            db.commit(bs.state, bs.code);

            MONAD_LOG_INFO(
                logger,
                "post_state: {}",
                monad::test::dump_state_from_db(db).dump());
            MONAD_LOG_INFO(
                logger,
                "finished transaction index: {} revision: {}, state_root: {}",
                case_index,
                fork_name,
                db.state_root());

            auto const msg = fmt::format(
                "fork_name: {}, case_index: {}", fork_name, case_index);

            EXPECT_EQ(db.state_root(), expected.state_hash) << msg;
            EXPECT_EQ(maybe_receipt.has_value(), !expected.exception) << msg;
            // TODO: assert something about receipt status?
        }
    }
}

void EthereumTests::TestBody()
{
    std::ifstream f{json_test_file_};

    auto const json = nlohmann::json::parse(f);
    auto const state_transition_test = EthereumTests::load_state_test(
        json, suite_name_, test_name_, file_name_, fork_index_, txn_index_);

    if (state_transition_test.cases.empty()) {
        MONAD_ASSERT(fork_index_.has_value() || txn_index_.has_value());
        GTEST_SKIP() << fmt::format(
            "No test cases found for fork={} txn={}",
            fork_index_.transform([&](auto const index) {
                return std::ranges::find(
                           fork_index_map,
                           index,
                           &decltype(fork_index_map)::value_type::second)
                    ->first;
            }),
            txn_index_);
    }
    EthereumTests::run_state_test(state_transition_test, json);
}

MONAD_TEST_NAMESPACE_END
