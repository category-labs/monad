#include <blockchain_test.hpp>
#include <ethereum_test.hpp>
#include <from_json.hpp>
#include <monad/core/assert.h>
#include <monad/execution/block_processor.hpp>
#include <monad/execution/test/fakes.hpp>
#include <monad/execution/transaction_processor_data.hpp>
#include <monad/logging/formatter.hpp>
#include <monad/rlp/decode_helpers.hpp>
#include <monad/state2/state.hpp>
#include <monad/test/config.hpp>
#include <test_resource_data.h>

#include <evmc/evmc.hpp>
#include <gtest/gtest.h>
#include <nlohmann/json.hpp>
#include <quill/Quill.h>

#include <algorithm>

MONAD_TEST_NAMESPACE_BEGIN

namespace
{
    template <typename TTraits>
    [[nodiscard]] std::vector<Receipt>
    execute(Block &block, test::db_t &db, execution::fake::BlockDb &block_cache)
    {
        using namespace monad::test;
        execution::AllTxnBlockProcessor processor;
        return processor.execute<
            mutex_t,
            TTraits,
            execution::TransactionProcessorFiberData<
                mutex_t,
                transaction_processor_t<TTraits>,
                host_t<TTraits>,
                execution::fake::BlockDb>>(block, db, block_cache);
    }

    [[nodiscard]] std::vector<Receipt> execute(
        evmc_revision const rev, Block &block, test::db_t &db,
        execution::fake::BlockDb &block_cache)
    {
        using namespace monad::fork_traits;

        switch (rev) {
        case EVMC_FRONTIER:
            return execute<frontier>(block, db, block_cache);
        case EVMC_HOMESTEAD:
            return execute<homestead>(block, db, block_cache);
        case EVMC_TANGERINE_WHISTLE:
            return execute<tangerine_whistle>(block, db, block_cache);
        case EVMC_SPURIOUS_DRAGON:
            return execute<spurious_dragon>(block, db, block_cache);
        case EVMC_BYZANTIUM:
            return execute<byzantium>(block, db, block_cache);
        case EVMC_PETERSBURG:
            return execute<constantinople_and_petersburg>(
                block, db, block_cache);
        case EVMC_ISTANBUL:
            return execute<istanbul>(block, db, block_cache);
        case EVMC_BERLIN:
            return execute<berlin>(block, db, block_cache);
        case EVMC_LONDON:
            return execute<london>(block, db, block_cache);
        case EVMC_PARIS:
            return execute<paris>(block, db, block_cache);
        case EVMC_SHANGHAI:
            return execute<shanghai>(block, db, block_cache);
        default:
            std::unreachable();
        }
    }
}

void BlockchainTest::TestBody()
{
    std::ifstream f{file_};

    auto const json = nlohmann::json::parse(f);
    bool executed = false;
    for (auto const &[name, j_contents] : json.items()) {
        auto const network = j_contents.at("network").get<std::string>();
        if (!revision_map.contains(network)) {
            LOG_ERROR(
                "Skipping {} due to missing support for network {}",
                name,
                network);
            continue;
        }

        auto const rev = revision_map.at(network);
        if (revision_.has_value() && rev != revision_) {
            continue;
        }

        executed = true;

        db_t db;
        {
            BlockState<mutex_t> bs;
            execution::fake::BlockDb fake_block_db;
            state::State state{bs, db, fake_block_db};
            load_state_from_json(j_contents.at("pre"), state);
            db.commit(state.state_, state.code_);
        }

        execution::fake::BlockDb fake_block_db;
        for (auto const &j_block : j_contents.at("blocks")) {
            Block block;
            auto const rlp = j_block.at("rlp").get<byte_string>();
            auto const rest = rlp::decode_block(block, rlp);
            EXPECT_TRUE(rest.empty()) << name;
            auto const receipts = execute(rev, block, db, fake_block_db);
            EXPECT_EQ(db.state_root(), block.header.state_root) << name;
            EXPECT_EQ(receipts.size(), block.transactions.size()) << name;
        }
    }

    if (!executed) {
        GTEST_SKIP() << "no test cases found";
    }
}

void register_blockchain_tests(std::optional<evmc_revision> const &revision)
{
    namespace fs = std::filesystem;

    // skip slow tests
    testing::FLAGS_gtest_filter +=
        ":-:BlockchainTests.GeneralStateTests/stTimeConsuming/*:"
        "BlockchainTests.GeneralStateTests/VMTests/vmPerformance/*:"
        "BlockchainTests.GeneralStateTests/stQuadraticComplexityTest/"
        "Call50000_sha256.json";

    constexpr auto suite = "BlockchainTests";
    auto const root = test_resource::ethereum_tests_dir / suite;
    for (auto const &entry : fs::recursive_directory_iterator{root}) {
        auto const path = entry.path();
        if (path.extension() == ".json") {
            MONAD_ASSERT(entry.is_regular_file());

            // get rid of minus signs, which is a special symbol when used in //
            // filtering
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
                    return new BlockchainTest(path, revision);
                });
        }
    }
}

MONAD_TEST_NAMESPACE_END
