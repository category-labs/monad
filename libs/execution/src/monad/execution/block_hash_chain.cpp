#include <monad/core/assert.h>
#include <monad/core/keccak.hpp>
#include <monad/core/rlp/monad_block_rlp.hpp>
#include <monad/db/db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_chain.hpp>
#include <monad/mpt/util.hpp>

MONAD_NAMESPACE_BEGIN

namespace
{
    bytes32_t
    get_eth_hash(mpt::Db const &db, uint64_t const n, mpt::NibblesView prefix)
    {
        auto const eth_header_query =
            db.get(mpt::concat(prefix, BLOCKHEADER_NIBBLE), n);
        MONAD_ASSERT_PRINTF(
            eth_header_query.has_value(),
            "Could not find eth_header at block %lu",
            n);
        return to_bytes(keccak256(eth_header_query.value()));
    }

    uint64_t get_parent(mpt::Db const &db, uint64_t n, mpt::NibblesView prefix)
    {
        auto const consensus_header_query =
            db.get(mpt::concat(prefix, BFT_BLOCK_NIBBLE), n);
        MONAD_ASSERT_PRINTF(
            consensus_header_query.has_value(),
            "Could not find consensus header at block %lu",
            n);
        byte_string_view view{consensus_header_query.value()};
        auto const consensus_header_decoded =
            rlp::decode_consensus_block_header(view);
        MONAD_ASSERT(consensus_header_decoded.has_value());
        return consensus_header_decoded.value().parent_round();
    }
}

BlockHashChain::BlockHashChain(mpt::Db const &db)
    : db_(db)
    , block_(mpt::INVALID_BLOCK_ID)
    , round_(0) {};

bytes32_t BlockHashChain::get(uint64_t const block) const
{
    uint64_t const earliest_blockhash_block = block_ < N ? 0 : block_ - N + 1;
    MONAD_ASSERT(block <= block_ && block >= earliest_blockhash_block);

    uint64_t const latest_finalized = db_.get_latest_finalized_block_id();
    MONAD_ASSERT(latest_finalized != mpt::INVALID_BLOCK_ID);

    if (block <= latest_finalized) {
        return get_eth_hash(db_, block, finalized_nibbles);
    }

    uint64_t b = block_;
    uint64_t r = round_;
    uint64_t last_r = r;

    do {
        auto const parent_round = get_parent(db_, b, proposal_prefix(r));

        last_r = r;
        b = b - 1;
        r = parent_round;
    }
    while (b >= block);
    return get_eth_hash(db_, block, proposal_prefix(last_r));
}

void BlockHashChain::set_block_and_round(
    uint64_t const block, std::optional<uint64_t> const round)
{
    block_ = block;
    round_ = round.value_or(0);
}

MONAD_NAMESPACE_END
