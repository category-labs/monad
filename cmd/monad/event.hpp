#pragma once

/**
 * @file
 *
 * Interface between `monad` and the event libraries
 */

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/result.hpp>

#include <cstddef>
#include <cstdint>
#include <span>
#include <string>
#include <string_view>
#include <variant>

MONAD_NAMESPACE_BEGIN

// clang-format off

struct EventRingConfig {
    std::string event_ring_path; ///< Path to shared memory file
    uint8_t ring_shift;          ///< Descriptor capacity == 2^(ring_shift)
    uint8_t payload_buf_shift;   ///< Buffer sz == 2^(payload_buffer_shift)
};

// clang-format on

constexpr uint8_t DEFAULT_EXECUTION_RECORDER_RING_SHIFT = 20;
constexpr uint8_t DEFAULT_EXECUTION_RECORDER_PAYLOAD_BUF_SHIFT = 28;

/// Parse an event ring configuration string of the form
/// `<file-path>[:<ring-shift>:<payload-buffer-shift>]`; if a parse
/// error occurs, returns a string describing the error
/// TODO(ken): this should return std::expected<EventRingConfig> instead, but
///    the combination of libstdc++ and <expected> requires clang19
std::variant<EventRingConfig, std::string>
    try_parse_event_ring_config(std::string_view);

/// Initializes an execution event ring with the given configuration options
int init_execution_event_recorder(EventRingConfig const &);

struct MonadConsensusBlockHeader;

/// Record the start of block execution: emits a BLOCK_START event and sets
/// the global block flow ID in the recording system
void record_block_exec_start(
    bytes32_t const &bft_block_id, MonadConsensusBlockHeader const &,
    size_t txn_count);

struct BlockExecOutput
{
    BlockHeader eth_header;
    bytes32_t eth_block_hash;
};

/// Record block execution output (or execution error) to the event system
/// and clear the active block flow ID
Result<BlockExecOutput> record_block_exec_result(Result<BlockExecOutput>);

MONAD_NAMESPACE_END
