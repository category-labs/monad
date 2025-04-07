#include <ethereum_test.hpp>
#include <from_json.hpp>
#include <test_resource_data.h>

#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
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
    struct EthereumMainnetRev : EthereumMainnet
    {
        evmc_revision const rev;

        EthereumMainnetRev(evmc_revision const rev)
            : rev{rev}
        {
        }

        virtual evmc_revision get_revision(
            uint64_t /* block_number */,
            uint64_t /* timestamp */) const override
        {
            return rev;
        }
    };
}

template <evmc_revision rev>
Result<std::vector<Receipt>> EthereumSpecTest::execute(
    Block &block, test::db_t &db, BlockHashBuffer const &block_hash_buffer)
{
    using namespace monad::test;

    BOOST_OUTCOME_TRY(static_validate_block<rev>(block));

    BlockState block_state(db);
    EthereumMainnetRev const chain{rev};
    BOOST_OUTCOME_TRY(
        auto const results,
        execute_block<rev>(
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
        MonadConsensusBlockHeader::from_eth_header(block.header),
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

Result<std::vector<Receipt>> EthereumSpecTest::execute_dispatch(
    evmc_revision const rev, Block &block, test::db_t &db,
    BlockHashBuffer const &block_hash_buffer)
{
    MONAD_ASSERT(rev != EVMC_CONSTANTINOPLE);
    SWITCH_EVMC_REVISION(execute, block, db, block_hash_buffer);
    MONAD_ASSERT(false);
}

void register_ethereum_blockchain_tests(
    std::optional<evmc_revision> const &revision)
{
    namespace fs = std::filesystem;

    // skip slow tests
    testing::FLAGS_gtest_filter +=
        ":-:BlockchainTests.GeneralStateTests/stTimeConsuming/*:"
        "BlockchainTests.GeneralStateTests/VMTests/vmPerformance/*:"
        "BlockchainTests.GeneralStateTests/stQuadraticComplexityTest/"
        "Call50000_sha256.json:"
        "BlockchainTests.ValidBlocks/bcForkStressTest/ForkStressTest.json";

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
                [=] { return new EthereumSpecTest(path, revision); });
        }
    }
}

MONAD_TEST_NAMESPACE_END
