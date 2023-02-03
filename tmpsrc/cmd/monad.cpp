#include <monad/db/block_db.hpp>
#include <monad/db/state_db.hpp>
#include <monad/execution/blockchain.hpp>

#include <silkworm/chain/config.hpp>
#include <silkworm/common/assert.hpp>
#include <silkworm/common/base.hpp>
#include <silkworm/common/directories.hpp>
#include <silkworm/common/log.hpp>
#include <silkworm/common/settings.hpp>
#include <silkworm/common/util.hpp>
#include <silkworm/db/access_layer.hpp>
#include <silkworm/db/buffer.hpp>
#include <silkworm/db/mdbx.hpp>
#include <silkworm/db/stages.hpp>
#include <silkworm/db/util.hpp>
#include <silkworm/types/block.hpp>
#include <silkworm/stagedsync/sync_loop_context.hpp>

#include <ethash/hash_types.hpp>

#include <evmc/evmc.hpp>

#include <CLI/CLI.hpp>

#include <filesystem>
#include <map>
#include <set>
#include <vector>

using namespace monad;

int main(int argc, char *argv[])
{
    CLI::App cli{"monad"};

    silkworm::log::Settings log_settings;
    silkworm::log::init(log_settings);
    silkworm::log::set_thread_name("main");

    std::filesystem::path data_dir =
        silkworm::DataDirectory::get_default_storage_path();

    cli.add_option("--datadir", data_dir, "data directory")
        ->capture_default_str();

    cli.parse(argc, argv);

    silkworm::NodeSettings node_settings;
    node_settings.data_directory =
        std::make_unique<silkworm::DataDirectory>(data_dir, true);
    node_settings.chaindata_env_config.path =
        node_settings.data_directory->chaindata().path().string();
    node_settings.chaindata_env_config.exclusive = true;

    node_settings.data_directory->deploy();

    auto chaindata_env =
        silkworm::db::open_env(node_settings.chaindata_env_config);
    auto txn{chaindata_env.start_write()};
    silkworm::db::RWTxn wrapped_txn{txn};

    node_settings.chain_config = silkworm::db::read_chain_config(txn);
    SILKWORM_ASSERT(node_settings.chain_config.has_value());
    node_settings.chain_config->seal_engine =
        silkworm::SealEngineType::kNoProof;

    BlockDb const block_db{node_settings.data_directory->block_db().path()};
    StateDb state_db{node_settings.data_directory->state_db().path()};
    silkworm::stagedsync::SyncLoopContext context { .txn = wrapped_txn, .state_db = state_db, };
    silkworm::db::Buffer buffer{block_db, context, 0};

    Blockchain blockchain{buffer, node_settings.chain_config.value()};

    auto const last_block = silkworm::db::stages::read_stage_progress(
        txn, silkworm::db::stages::kExecutionKey);

    unsigned tx_count = 0;
    for (silkworm::BlockNum i = last_block + 1; i < last_block + 101; ++i) {
        silkworm::Block block;
        if (!block_db.get(i, block)) {
            break;
        }
        silkworm::log::Info() << "block " << i << " with "
                              << block.transactions.size() << " txns ";
        ValidationResult const validate_result =
            blockchain.pre_validate_block(block);
        if (validate_result != ValidationResult::kOk) {
            silkworm::log::Error() << "failed to validate block " << i;
            break;
        }
        else {
            silkworm::log::Info() << "validated block " << i;
        }
        std::vector<Receipt> receipts;
        ValidationResult const execution_result =
            blockchain.execute_block(block, receipts);
        if (validate_result == ValidationResult::kOk) {
            buffer.insert_receipts(i, receipts);
            silkworm::log::Info() << "executed block " << i;
        }
        else {
            silkworm::log::Info() << "failed to execute block " << i;
        }
        tx_count += block.transactions.size();
        if (tx_count >= 10000) {
            break;
        }
    }

    silkworm::log::Info() << "num tx = " << tx_count;

    silkworm::log::Info() << "account changes";
    std::set<evmc::address> account_changes;
    for (auto const &[block_num, addresses] : buffer.account_changes()) {
        for (auto const &[address, account] : addresses) {
            account_changes.insert(address);
        }
    }
    for (auto const &[block_num, addresses] : buffer.storage_changes()) {
        for (auto const &[address, incarnations] : addresses) {
            account_changes.insert(address);
        }
    }
    std::map<evmc::address, ethash::hash256> account_changes_hashed;
    unsigned i = 0;
    uint64_t total_time = 0;
    for (auto const &address : account_changes) {
        auto const begin = std::chrono::steady_clock::now();
        auto const result = silkworm::keccak256(address.bytes);
        auto const end = std::chrono::steady_clock::now();
        auto const duration =
            std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin)
                .count();
        total_time += duration;
        ++i;
        account_changes_hashed[address] = result;
    }
    silkworm::log::Info() << "account changes "
                          << account_changes_hashed.size();
    silkworm::log::Info() << "average time = " << (total_time / i) << " ns";

    return 0;
}
