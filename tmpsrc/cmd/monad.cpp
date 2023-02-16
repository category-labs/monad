#include <monad/db/block_db.hpp>
#include <monad/db/state_db.hpp>
#include <monad/execution/blockchain.hpp>
#include <monad/execution/execution.hpp>
#include <monad/execution/hashstate.hpp>
#include <monad/execution/interhash.hpp>

#include <silkworm/common/assert.hpp>
#include <silkworm/db/access_layer.hpp>

#include <CLI/CLI.hpp>

#include <filesystem>

using namespace monad;

int main(int argc, char *argv[])
{
    CLI::App cli{"monad"};

    silkworm::log::Settings log_settings;
    silkworm::log::init(log_settings);
    silkworm::log::set_thread_name("main");

    std::filesystem::path data_dir =
        silkworm::DataDirectory::get_default_storage_path();

    unsigned num_blocks = 1;

    cli.add_option("--datadir", data_dir, "data directory")
        ->capture_default_str();

    cli.add_option("--blocks", num_blocks, "number of blocks");

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
    silkworm::db::RWTxn txn{chaindata_env};

    node_settings.chain_config = silkworm::db::read_chain_config(*txn);
    SILKWORM_ASSERT(node_settings.chain_config.has_value());
    node_settings.chain_config->seal_engine =
        silkworm::SealEngineType::kNoProof;

    silkworm::stagedsync::StageResult stage_result{};
    silkworm::stagedsync::MonadExecution execution_stage(&node_settings);
    silkworm::stagedsync::MonadHashState hash_stage(&node_settings);
    silkworm::stagedsync::MonadInterHashes interhashes_stage(&node_settings);
    for (silkworm::BlockNum i = 0; i < num_blocks; ++i)
    {
        silkworm::log::Info() << "Executing: " << i;
        stage_result = execution_stage.forward(txn);
        assert(stage_result == silkworm::stagedsync::StageResult::kSuccess);
        silkworm::log::Info() << "Hashing: " << i;
        stage_result = hash_stage.forward(txn);
        assert(stage_result == silkworm::stagedsync::StageResult::kSuccess);
        silkworm::log::Info() << "Intermediate Hashing: " << i;
        stage_result = interhashes_stage.forward(txn);
        assert(stage_result == silkworm::stagedsync::StageResult::kSuccess);
    }
    
    return 0;
}
