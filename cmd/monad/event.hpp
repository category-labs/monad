#pragma once

/**
 * @file
 *
 * Interface between `monad` and the event libraries
 */

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/result.hpp>
#include <monad/event/event_ring_db.h>

#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <map>
#include <span>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

MONAD_NAMESPACE_BEGIN

// clang-format off

struct EventRingConfig {
    monad_event_ring_type ring_type; ///< Config applies to this ring type
    bool enabled;                    ///< True => enable the event ring
    uint8_t ring_shift;              ///< Descriptor capacity == 2^(ring_shift)
    uint8_t payload_buffer_shift;    ///< Buffer sz == 2^(payload_buffer_shift)
};

// clang-format on

extern EventRingConfig const DefaultEventRingConfig[MONAD_EVENT_RING_COUNT];

/// Parse an event ring configuration string of the form
/// `<ring-type>:<enabled>[:<ring-shift>:<payload-buffer-shift>]`; if a parse
/// error occurs, returns a string describing the error
/// TODO(ken): this should return std::expected<EventRingConfig> instead, but
///    the combination of libstdc++ and <expected> requires clang19
std::variant<EventRingConfig, std::string>
    try_parse_event_ring_config(std::string_view);

/// Initializes the event rings with the given configuration options
int init_event_system(
    std::span<EventRingConfig const>, char const *shm_name,
    monad_event_ring_db **);

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

struct Receipt;
struct Transaction;

namespace event_cross_validation_test
{
    class ExpectedDataRecorder
    {
    public:
        explicit ExpectedDataRecorder(std::filesystem::path const &);
        ~ExpectedDataRecorder();

        void record_execution(
            bytes32_t const &bft_block_id, bytes32_t const &eth_block_hash,
            MonadConsensusBlockHeader const &input_header,
            BlockHeader const &output_header, std::span<Transaction const>,
            std::span<Receipt const>, std::span<Address const> senders);

        void record_finalization(
            uint64_t consensus_seqno, bytes32_t const &bft_block_id);

    private:
        std::FILE *file_;
        size_t array_size_;
        std::map<uint64_t, std::vector<bytes32_t>> pending_blocks_;
    };
} // namespace event_round_trip_test

MONAD_NAMESPACE_END
