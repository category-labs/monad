#include <monad/core/assert.h>
#include <monad/core/blake3.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/util.hpp>
#include <monad/emitter/execution_graph_emitter.hpp>
#include <monad/mpt/db.hpp>

#include <evmc/evmc.hpp>

#include <fstream>

MONAD_NAMESPACE_BEGIN

namespace
{
    byte_string slurp_file(std::filesystem::path const &path)
    {
        MONAD_ASSERT(
            std::filesystem::exists(path) &&
            std::filesystem::is_regular_file(path));
        std::ifstream is(path);
        MONAD_ASSERT(is);
        return {
            std::istreambuf_iterator<char>(is),
            std::istreambuf_iterator<char>()};
    }
}

ExecutionGraphEmitter::ExecutionGraphEmitter(
    uint64_t const last_finalized_round,
    std::filesystem::path const &ledger_dir, mpt::Db &db)
    : last_finalized_round_{last_finalized_round}
    , ledger_dir_{ledger_dir}
    , db_{db}
{
}

bool ExecutionGraphEmitter::has_executed(
    ConsensusBlockHeader const &header) const
{
    auto const query_res = db_.get(
        mpt::concat(PROPOSAL_NIBBLE, mpt::NibblesView{bft_block_nibbles}),
        header.proposed.number);
    if (MONAD_LIKELY(query_res.has_error())) {
        // does not exist
        return false;
    }

    // duplicate proposal for round
    byte_string_view view{query_res.value()};
    auto decode_res = rlp::decode_consensus_block_header(view);
    MONAD_ASSERT(!decode_res.has_error());
    return decode_res.value() == header;
}

void ExecutionGraphEmitter::populate_chain(
    std::string_view const read_head, std::deque<ConsensusBlockHeader> &chain,
    uint64_t const stop_round)
{
    std::filesystem::path next = ledger_dir_ / read_head;
    while (true) {
        auto const data = slurp_file(next);
        byte_string_view view{data};
        auto res = rlp::decode_consensus_block_header(view);
        MONAD_ASSERT(!res.has_error());

        auto header = std::move(res.assume_value());
        if (header.round <= stop_round) {
            break;
        }
        next = ledger_dir_ / evmc::hex(header.parent_bft_block_id);
        chain.push_back(std::move(header));
    }
}

std::pair<BlockEmitter::Action, ConsensusBlock>
ExecutionGraphEmitter::pop_execute()
{
    // deliberate copy, because on execute the item stays in the chain.
    auto header = to_execute_.back();

    auto const data = slurp_file(ledger_dir_ / evmc::hex(header.block_body_id));
    byte_string_view view{data};
    MONAD_ASSERT(to_bytes(blake3(view)) == header.block_body_id);
    auto res = rlp::decode_consensus_block_body(view);
    MONAD_ASSERT(!res.has_error());

    auto body = res.assume_value();
    Action action;
    if (has_executed(header)) {
        // only remove from chain on finalize
        last_finalized_round_ = header.round;
        action = Action::FINALIZE;
        to_execute_.pop_back();
    }
    else {
        last_proposed_round_ = header.round;
        action = Action::EXECUTE;
    }
    return std::make_pair(
        action,
        ConsensusBlock{.header = std::move(header), .body = std::move(body)});
}

std::pair<BlockEmitter::Action, ConsensusBlock>
ExecutionGraphEmitter::pop_optimistic_execute()
{
    auto header = std::move(to_execute_optimistic_.back());
    to_execute_optimistic_.pop_back();

    auto const data = slurp_file(ledger_dir_ / evmc::hex(header.block_body_id));
    byte_string_view view{data};
    MONAD_ASSERT(to_bytes(blake3(view)) == header.block_body_id);
    auto res = rlp::decode_consensus_block_body(view);
    MONAD_ASSERT(!res.has_error());

    auto body = res.assume_value();
    last_proposed_round_ = header.round;
    return std::make_pair(
        Action::EXECUTE,
        ConsensusBlock{.header = std::move(header), .body = std::move(body)});
}

std::optional<std::pair<BlockEmitter::Action, ConsensusBlock>>
ExecutionGraphEmitter::next_block()
{
    if (to_execute_.empty()) {
        populate_chain("finalized_head", to_execute_, last_finalized_round_);
    }
    if (!to_execute_.empty()) {
        to_execute_optimistic_.clear();
        return pop_execute();
    }

    if (to_execute_optimistic_.empty()) {
        populate_chain(
            "proposals_head", to_execute_optimistic_, last_proposed_round_);
    }
    if (!to_execute_optimistic_.empty()) {
        return pop_optimistic_execute();
    }
    return std::nullopt;
}

MONAD_NAMESPACE_END
