#include <ethereum_test.hpp>
#include <from_json.hpp>
#include <general_state_test.hpp>
#include <general_state_test_types.hpp>

#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/core/signature.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>
#include <monad/test/config.hpp>
#include <monad/test/dump_state_from_db.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <quill/bundled/fmt/core.h>
#include <quill/detail/LogMacros.h>

#include <test_resource_data.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>
#include <stdexcept>
#include <utility>

using namespace monad;

namespace
{
    constexpr BlockHeader block_header_from_env(nlohmann::json const &json)
    {
        BlockHeader o;
        o.parent_hash = json["previousHash"].get<monad::bytes32_t>();
        o.difficulty = json["currentDifficulty"].get<monad::uint256_t>();
        o.number = static_cast<uint64_t>(
            json["currentNumber"].get<monad::uint256_t>());
        o.gas_limit = static_cast<uint64_t>(
            json["currentGasLimit"].get<monad::uint256_t>());
        o.timestamp = static_cast<uint64_t>(
            json["currentTimestamp"].get<monad::uint256_t>());
        o.beneficiary = json["currentCoinbase"].get<monad::Address>();

        // we cannot use the nlohmann::json from_json<uint64_t> because
        // it does not use the strtoull implementation, whereas we need
        // it so we can turn a hex string into a uint64_t
        o.base_fee_per_gas =
            json.contains("currentBaseFee")
                ? std::make_optional<uint64_t>(
                      integer_from_json<uint64_t>(json["currentBaseFee"]))
                : std::nullopt;

        o.prev_randao = json["currentRandom"].get<monad::bytes32_t>();
        return o;
    }

    template <typename Traits>
    Result<Receipt> execute(
        BlockHeader const &block_header, State &state, Transaction const &tx)
    {
        using namespace monad::test;

        // sum of transaction gas limit and gas utilized in block prior (0 in
        // this case) must be no greater than the blocks gas limit
        if (block_header.gas_limit < tx.gas_limit) {
            return TransactionError::GasLimitReached;
        }

        BlockHashBuffer block_hash_buffer;
        MONAD_ASSERT(block_header.number);
        block_hash_buffer.set(
            block_header.number - 1, block_header.parent_hash);

        return validate_and_execute<Traits::rev>(
            tx, block_header, block_hash_buffer, state);
    }

    Result<Receipt> execute_dispatch(
        evmc_revision const rev, BlockHeader const &block_header, State &state,
        Transaction const &txn)
    {
        using namespace monad::fork_traits;

        auto result = [&] {
            switch (rev) {
            case EVMC_FRONTIER:
                return execute<frontier>(block_header, state, txn);
            case EVMC_HOMESTEAD:
                return execute<homestead>(block_header, state, txn);
            case EVMC_TANGERINE_WHISTLE:
                return execute<tangerine_whistle>(block_header, state, txn);
            case EVMC_SPURIOUS_DRAGON:
                return execute<spurious_dragon>(block_header, state, txn);
            case EVMC_BYZANTIUM:
                return execute<byzantium>(block_header, state, txn);
            case EVMC_PETERSBURG:
                return execute<constantinople_and_petersburg>(
                    block_header, state, txn);
            case EVMC_ISTANBUL:
                return execute<istanbul>(block_header, state, txn);
            case EVMC_BERLIN:
                return execute<berlin>(block_header, state, txn);
            case EVMC_LONDON:
                return execute<london>(block_header, state, txn);
            case EVMC_PARIS:
                return execute<paris>(block_header, state, txn);
            case EVMC_SHANGHAI:
                return execute<shanghai>(block_header, state, txn);
            default:
                MONAD_ASSERT(false);
            }
        }();

        // Apply 0 block reward
        if (rev < EVMC_SPURIOUS_DRAGON) {
            state.add_to_balance(block_header.beneficiary, 0);
        }

        return result;
    }
}

MONAD_TEST_NAMESPACE_BEGIN

void GeneralStateTest::TestBody()
{
    std::ifstream f{json_test_file_};

    auto const json = nlohmann::json::parse(f);

    if (!json.is_object()) {
        throw std::invalid_argument{fmt::format(
            "Error parsing {}: expected a JSON object", json_test_file_)};
    }

    if (json.empty()) {
        throw std::invalid_argument{fmt::format(
            "Error parsing {}: expected a non-empty JSON object",
            json_test_file_)};
    }

    auto const &test = *json.begin();

    auto const data = test.at("transaction").get<SharedTransactionData>();
    auto const env = block_header_from_env(test.at("env"));

    auto const [init_state, init_code] = [&] {
        db_t db;
        BlockState bs{db};
        State state{bs};
        load_state_from_json(test.at("pre"), state);
        return std::make_pair(state.state_, state.code_);
    }();

    bool executed = false;

    for (auto const &[rev_name, expectations] : test.at("post").items()) {
        if (!revision_map.contains(rev_name)) {
            LOG_ERROR("Unsupported fork {} in {}", rev_name, json_test_file_);
            continue;
        }

        auto const rev = revision_map.at(rev_name);
        if (revision_.has_value() && rev != revision_) {
            continue;
        }

        auto const block_header = [&] {
            auto ret = env;
            // eip-1559, base fee only introduced in london
            if (rev < EVMC_LONDON) {
                ret.base_fee_per_gas.reset();
            }

            // eip-4399, difficulty set to 0 in PoS
            if (rev >= EVMC_PARIS) {
                ret.difficulty = 0;
            }

            return ret;
        }();

        for (size_t i = 0; i < expectations.size(); ++i) {
            if (txn_index_.has_value() && txn_index_ != i) {
                continue;
            }

            LOG_INFO("Executing txn {} on revision {}", i, rev_name);

            executed = true;

            auto const expected = expectations.at(i).get<Expectation>();
            auto const transaction = Transaction{
                .sc =
                    SignatureAndChain{
                        .r = {},
                        .s = {},
                        // Only supporting mainnet for now
                        .chain_id = rev >= EVMC_SPURIOUS_DRAGON
                                        ? std::make_optional(1)
                                        : std::nullopt},
                .nonce = data.nonce,
                .max_fee_per_gas = data.max_fee_per_gas,
                .gas_limit = data.gas_limits.at(expected.indices.gas_limit),
                .value = data.values.at(expected.indices.value),
                .to = data.to,
                .from = data.sender,
                .data = data.inputs.at(expected.indices.input),
                .type = data.transaction_type,
                .access_list =
                    data.access_lists.empty()
                        ? AccessList{}
                        : data.access_lists.at(expected.indices.input),
                .max_priority_fee_per_gas =
                    rev < EVMC_LONDON
                        ? 0
                        : data.max_priority_fee_per_gas /*eip-1559*/};

            db_t db;
            db.commit(init_state, init_code);
            BlockState bs{db};
            State state{bs};
            auto const result =
                execute_dispatch(rev, block_header, state, transaction);
            // Note: no merge because only single transaction in the block
            db.commit(state.state_, state.code_);

            LOG_DEBUG("post_state: {}", test::dump_state_from_db(db).dump());

            auto const msg = fmt::format("fork: {}, index: {}", rev_name, i);

            if (!result.has_error()) {
                EXPECT_EQ(expected.error, TransactionError::Success) << msg;
            }
            else {
                EXPECT_EQ(result.error(), expected.error) << msg;
            }

            // TODO: assert something about receipt status?

            EXPECT_EQ(db.state_root(), expected.state_hash) << msg;
        }
    }

    // Be explicit about skipping the test rather than succeeding due to
    // no-op
    if (!executed) {
        MONAD_ASSERT(revision_.has_value() || txn_index_.has_value());
        GTEST_SKIP() << fmt::format(
            "No test cases found for fork={} txn={}",
            revision_.transform(
                [](auto const &revision) { return evmc::to_string(revision); }),
            txn_index_);
    }
}

void register_general_state_tests(
    std::optional<evmc_revision> const &revision,
    std::optional<size_t> const &txn_index)
{
    namespace fs = std::filesystem;

    // The default test filter. To enable all tests use `--gtest_filter=*`.
    testing::FLAGS_gtest_filter +=
        ":-:GeneralStateTests.stCreateTest/CreateOOGafterMaxCodesize.json:" // slow test
        "GeneralStateTests.stQuadraticComplexityTest/Call50000_sha256.json:" // slow test
        "GeneralStateTests.stTimeConsuming/static_Call50000_sha256.json:" // slow
                                                                          // test
        "GeneralStateTests.stTimeConsuming/CALLBlake2f_MaxRounds.json:" // slow
                                                                        // test
        "GeneralStateTests.VMTests/vmPerformance/*:" // slow test

        // this test causes the test harness to crash when
        // parsing because it tries to parse
        // "0x031eea408f8e1799cb883da2927b1336521d73c2c14accfebb70d5c5af006c"
        // which causes stoull to throw an std::out_of_range exception
        "GeneralStateTests.stTransactionTest/HighGasPrice.json:"
        "GeneralStateTests.stTransactionTest/ValueOverflow.json";

    constexpr auto suite = "GeneralStateTests";
    auto const root = test_resource::ethereum_tests_dir / suite;
    for (auto const &entry : fs::recursive_directory_iterator{root}) {
        auto const path = entry.path();
        if (path.extension() == ".json") {
            MONAD_ASSERT(entry.is_regular_file());

            // Normalize the test name so that gtest_filter can recognize
            // it. ie.
            // stZeroKnowledge2.ecmul_0-3_5616_21000_128 will
            // not work because gtest interprets the minus sign as exclusion

            auto test = fmt::format("{}", fs::relative(path, root).string());
            std::ranges::replace(test, '-', '_');

            testing::RegisterTest(
                suite,
                test.c_str(),
                nullptr,
                nullptr,
                path.string().c_str(),
                0,
                [=] -> testing::Test * {
                    return new GeneralStateTest(path, revision, txn_index);
                });
        }
    }
}

MONAD_TEST_NAMESPACE_END
