#include <from_json.hpp>
#include <monad_spec_test.hpp>
#include <spec_test_utils.hpp>
#include <test_resource_data.h>

#include <monad/chain/monad_chain.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_monad_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/switch_evmc_revision.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/state3/state.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.h>
#include <gtest/gtest.h>
#include <quill/bundled/fmt/core.h>
#include <quill/bundled/fmt/format.h>
#include <quill/detail/LogMacros.h>

#include <cstdint>

MONAD_TEST_NAMESPACE_BEGIN

namespace
{
    struct MonadChainRev : public MonadChain
    {
        virtual uint256_t get_chain_id() const override
        {
            return 1;
        }

        virtual monad_revision get_monad_revision(
            uint64_t /* block_number */,
            uint64_t /* timestamp */) const override
        {
            return MONAD_TWO;
        }
    };
}

template <evmc_revision rev>
Result<std::vector<Receipt>> MonadSpecTest::execute(
    Block &block, test::db_t &db, BlockHashBuffer const &block_hash_buffer)
{
    using namespace monad::test;

    BOOST_OUTCOME_TRY(static_validate_block<rev>(block));

    auto const consensus_header =
        MonadConsensusBlockHeader::from_eth_header(block.header);

    BlockState block_state(db);
    MonadChainRev const chain;
    BOOST_OUTCOME_TRY(
        auto const results,
        execute_monad_block<rev>(
            chain, block, block_state, block_hash_buffer, *pool_));
    std::vector<Receipt> receipts(results.size());
    std::vector<std::vector<CallFrame>> call_frames(results.size());
    std::vector<Address> senders(results.size());
    for (unsigned i = 0; i < results.size(); ++i) {
        receipts[i] = std::move(results[i].receipt);
        call_frames[i] = std::move(results[i].call_frames);
        senders[i] = results[i].sender;
    }

    block_state.log_debug();
    block_state.commit(
        consensus_header,
        receipts,
        call_frames,
        senders,
        block.transactions,
        block.ommers,
        block.withdrawals);
    db.finalize(block.header.number, block.header.number);

    auto output_header = db.read_eth_header();
    BOOST_OUTCOME_TRY(
        chain.validate_output_header(block.header, output_header));

    return receipts;
}

Result<std::vector<Receipt>> MonadSpecTest::execute_dispatch(
    evmc_revision const rev, Block &block, test::db_t &db,
    BlockHashBuffer const &block_hash_buffer)
{
    MONAD_ASSERT(rev != EVMC_CONSTANTINOPLE);
    SWITCH_EVMC_REVISION(execute, block, db, block_hash_buffer);
    MONAD_ASSERT(false);
}

fiber::PriorityPool *MonadSpecTest::pool_ = nullptr;

void MonadSpecTest::SetUpTestSuite()
{
    pool_ = new fiber::PriorityPool{1, 1};
}

void MonadSpecTest::TearDownTestSuite()
{
    delete pool_;
    pool_ = nullptr;
}

void MonadSpecTest::TestBody()
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

        InMemoryMachine machine;
        mpt::Db db{machine};
        db_t tdb{db};
        load_genesis_json_into_db(rev, j_contents, tdb);
        auto db_post_state = tdb.to_json();

        BlockHashBufferFinalized block_hash_buffer;
        for (auto const &j_block : j_contents.at("blocks")) {
            auto const block_rlp = j_block.at("rlp").get<byte_string>();
            byte_string_view block_rlp_view{block_rlp};
            auto block = rlp::decode_block(block_rlp_view);
            if (block.has_error() || !block_rlp_view.empty()) {
                EXPECT_TRUE(j_block.contains("expectException")) << name;
                continue;
            }

            if (block.value().header.number == 0) {
                EXPECT_TRUE(j_block.contains("expectException"));
                continue;
            }
            if (j_block.contains("blocknumber") &&
                block.value().header.number !=
                    std::stoull(j_block.at("blocknumber").get<std::string>())) {
                EXPECT_TRUE(j_block.contains("expectException"));
                continue;
            }

            block_hash_buffer.set(
                block.value().header.number - 1,
                block.value().header.parent_hash);

            auto const result =
                execute_dispatch(rev, block.value(), tdb, block_hash_buffer);
            if (!result.has_error()) {
                db_post_state = tdb.to_json();
                EXPECT_FALSE(j_block.contains("expectException"));
            }
            else {
                EXPECT_TRUE(j_block.contains("expectException"))
                    << result.error().message().c_str();
            }
        }

        bool const has_post_state = j_contents.contains("postState");
        if (has_post_state) {
            validate_post_state(j_contents.at("postState"), db_post_state);
        }
        LOG_DEBUG("post_state: {}", db_post_state.dump());
    }

    if (!executed) {
        MONAD_ASSERT(revision_.has_value());
        GTEST_SKIP() << "no test cases found revision=" << revision_.value();
    }
}

void register_monad_blockchain_tests(
    std::optional<evmc_revision> const &revision)
{
    namespace fs = std::filesystem;

    constexpr auto suite = "MonadBlockchainTests";
    auto const root = test_resource::monad_tests_dir / suite;
    std::cout << "root:" << root << std::endl;
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
                [=] { return new MonadSpecTest(path, revision); });
        }
    }
}

MONAD_TEST_NAMESPACE_END
