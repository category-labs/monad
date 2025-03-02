#pragma once

/**
 * @file
 *
 * Interface between `monad` and the event ring library
 */

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/result.hpp>

#include <cstddef>
#include <cstdint>
#include <expected>
#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

struct MonadConsensusBlockHeader;

// clang-format off

struct EventRingConfig
{
    std::string event_ring_path; ///< Path to shared memory file
    uint8_t descriptors_shift;   ///< Descriptor capacity = 2^descriptors_shift
    uint8_t payload_buf_shift;   ///< Payload buffer size = 2^payload_buf_shift
};

// clang-format on

// General advice for setting the default ring parameters below: the average
// event payload length (at the time of this writing) is about 200 bytes, close
// to 256 (2^8). Thus, the default payload buffer shift is equal to the default
// descriptor shift plus 8. At current rates a block generates about 1MiB of
// event data on average, so the below size keeps a few minutes worth of
// history and gives a large amount of slack for slow consumers. These values
// are likely to change in the future, you can view current numbers using the
// `eventcap execstats` subcommand
constexpr uint8_t DEFAULT_EXEC_RING_DESCRIPTORS_SHIFT = 21;
constexpr uint8_t DEFAULT_EXEC_RING_PAYLOAD_BUF_SHIFT = 29;

/// Parse an event ring configuration string of the form
/// `<file-path>[:<ring-shift>:<payload-buffer-shift>]`; if a parse
/// error occurs, returns a string describing the error
std::expected<EventRingConfig, std::string>
    try_parse_event_ring_config(std::string_view);

/// Initializes the global recorder object for the execution event ring (an
/// object inside libmonad_execution) with the given configuration options
int init_execution_event_recorder(EventRingConfig const &);

/// Record the start of block execution: emits a BLOCK_START event and sets the
/// global block flow sequence number in the recorder; also emits a BLOCK_QC
/// corresponding to the QC for the parent block this proposal is built upon
void record_block_exec_start(
    bytes32_t const &bft_block_id, uint256_t const &chain_id,
    MonadConsensusBlockHeader const &, bytes32_t const &eth_parent_hash,
    size_t txn_count);

/// Record a BLOCK_FINALIZE event for the given proposal, and one
/// BLOCK_VERIFIED event for each block number referenced in the
/// `delayed_execution_results` field of the consensus header
void record_block_finalized(
    bytes32_t const &bft_block_id, MonadConsensusBlockHeader const &);

/// Named pair holding the Ethereum block execution outputs
struct BlockExecOutput
{
    BlockHeader eth_header;
    bytes32_t eth_block_hash;
};

/// Record block execution output events (or an execution error event, if
/// Result::has_error() is true); also clears the active block flow ID
Result<BlockExecOutput> record_block_exec_result(Result<BlockExecOutput>);

MONAD_NAMESPACE_END
