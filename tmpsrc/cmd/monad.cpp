#include <monad/db/block_db.hpp>
#include <monad/db/state_db.hpp>

#include <silkworm/common/assert.hpp>

#include <silkworm/stagedsync/mem_stage_execution.hpp>
#include <silkworm/stagedsync/mem_stage_flush.hpp>
#include <silkworm/stagedsync/mem_stage_interhashes.hpp>
#include <silkworm/db/access_layer.hpp>
#include <silkworm/db/buffer.hpp>
#include <silkworm/common/stopwatch.hpp>

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
    unsigned eth_blocks_per_monad_block = 100;

    cli.add_option("--datadir", data_dir, "data directory")
        ->capture_default_str();
    cli.add_option("--blocks", num_blocks, "number of monad blocks to forward");
    cli.add_option("--per-monad", eth_blocks_per_monad_block, "number of ethereum blocks per monad block");
    auto *time_it = cli.add_flag("--time-it", "time the run loop");

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

    BlockDb const block_db{node_settings.data_directory->block_db().path()};
    StateDb state_db{node_settings.data_directory->state_db().path()};
    silkworm::db::Buffer buffer(block_db, state_db, *txn, 0, std::nullopt, true);

    silkworm::stagedsync::StageResult stage_result{};
    auto next_block_num{silkworm::db::stages::read_stage_progress(*txn, silkworm::db::stages::kExecutionKey)};
    silkworm::stagedsync::MemExecution execution_stage(&node_settings, eth_blocks_per_monad_block);
    silkworm::stagedsync::MemFlush flush_stage(&node_settings);
    silkworm::stagedsync::MemInterHashes interhashes_stage(&node_settings);

    std::chrono::_V2::steady_clock::time_point start_time{};
    std::chrono::_V2::steady_clock::time_point execution_start_time{};
    std::chrono::_V2::steady_clock::time_point flush_start_time{};
    std::chrono::_V2::steady_clock::time_point interhash_start_time{};

    start_time = std::chrono::steady_clock::now();
    uint64_t total_txns_count = 0u;
    silkworm::log::Info() << "Execution Begin";
    for (silkworm::BlockNum i = 0; i < num_blocks; ++i)
    {
        execution_start_time = std::chrono::steady_clock::now();
        silkworm::log::Info("Begin Executing Monad Block " + std::to_string(i+1), {"silkworm_block_from", std::to_string(next_block_num+1), "silkworm_block_to", std::to_string(next_block_num + eth_blocks_per_monad_block)});

        if (*time_it) {
            silkworm::log::Info() << "Begin Stage Execution";
        }
        stage_result = execution_stage.run(txn, block_db, buffer, next_block_num + 1);
        assert(stage_result == silkworm::stagedsync::StageResult::kSuccess);
        next_block_num += eth_blocks_per_monad_block;
        uint64_t txns_count = execution_stage.txns_last_block();
        total_txns_count += txns_count;
        if (*time_it) {
            auto time_elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - execution_start_time);
            silkworm::log::Info("Finish Stage Execution",{"time", silkworm::StopWatch::format(time_elapsed), "txns", std::to_string(txns_count), "txns/s",  std::to_string(txns_count*1000 / time_elapsed.count())});
        }

        if(*time_it){
            flush_start_time = std::chrono::steady_clock::now();
            silkworm::log::Info() << "Begin Stage Flushing";
        }
        stage_result = flush_stage.run(txn, block_db, buffer, next_block_num);
        assert(stage_result == silkworm::stagedsync::StageResult::kSuccess);
        if (*time_it) {
            auto time_elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - flush_start_time);
            silkworm::log::Info("Finish Stage Flushing", {"time", silkworm::StopWatch::format(time_elapsed)});
        }
        if(*time_it){
            interhash_start_time = std::chrono::steady_clock::now();
            silkworm::log::Info() << "Begin Stage Intermediate Hashing";
        }
        stage_result = interhashes_stage.run(txn, block_db, buffer, next_block_num);
        assert(stage_result == silkworm::stagedsync::StageResult::kSuccess);
        if (*time_it) {
            auto time_elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - interhash_start_time);
            silkworm::log::Info("Finish Stage Intermediate Hashing", {"time", silkworm::StopWatch::format(time_elapsed)});
        }

        auto monad_block_end_time{std::chrono::steady_clock::now()};
        auto time_elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(monad_block_end_time - execution_start_time);
        silkworm::log::Info("Run loop iteration " + std::to_string(i+1), {"time", silkworm::StopWatch::format(time_elapsed), "txns/s", std::to_string(txns_count*1'000 / (time_elapsed).count())});
    }
    
    auto end_time{std::chrono::steady_clock::now()};
    auto time_elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time);
    silkworm::log::Info("All run loop iterations", {"time", silkworm::StopWatch::format(time_elapsed), "txns/s", std::to_string(total_txns_count*1'000 / (time_elapsed).count())});
    
    return 0;
}