#pragma once

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/result.hpp>
#include <monad/event/event.h>
#include <monad/execution/execute_transaction.hpp>

#include <cstdint>
#include <filesystem>
#include <span>
#include <thread>

struct monad_event_server;
extern "C" void monad_event_server_destroy(monad_event_server *);

MONAD_NAMESPACE_BEGIN

// clang-format off

struct EventRingConfig {
    bool enabled;                  ///< This event ring is enabled
    uint8_t ring_shift;            ///< Descriptor capacity == 2^(ring_shift)
    uint8_t payload_buffer_shift;  ///< Buffer size == 2^(payload_buffer_shift)
};

// clang-format on

extern EventRingConfig const DefaultEventRingConfig[MONAD_EVENT_RING_COUNT];

extern std::jthread init_event_system(
    std::span<EventRingConfig const, MONAD_EVENT_RING_COUNT>,
    std::filesystem::path const &event_socket_path, monad_event_server **);

struct MonadConsensusBlockHeader;

extern monad_event_block_exec_header *init_block_exec_header(
    bytes32_t const &bft_block_id, MonadConsensusBlockHeader const &,
    size_t txn_count, monad_event_block_exec_header *exec_header);

extern monad_event_block_exec_result *init_block_exec_result(
    bytes32_t const &hash, BlockHeader const &,
    monad_event_block_exec_result *);

struct BlockExecOutput
{
    BlockHeader eth_header;
    bytes32_t eth_block_hash;
    std::vector<ExecutionResult> tx_exec_results;
};

// Record block execution output errors to the event system if it is present,
// otherwise records an appropriate error event
extern Result<BlockExecOutput>
    try_record_block_exec_output(Result<BlockExecOutput>);

MONAD_NAMESPACE_END
