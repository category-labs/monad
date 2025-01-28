#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/mpt/db.hpp>
#include <monad/statesync/statesync_server_context.hpp>

#include <quill/Quill.h>

#include <algorithm>
#include <cstdint>
#include <mutex>

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

void on_commit(
    monad_statesync_server_context &ctx, StateDeltas const &state_deltas,
    uint64_t const n, uint64_t const round)
{
    auto &proposals = ctx.proposals;
    auto it = std::find_if(
        proposals.begin(), proposals.end(), [round](auto const &p) {
            return p.round == round;
        });

    if (MONAD_UNLIKELY(it != proposals.end())) {
        proposals.erase(it);
    }
    auto &deletions =
        proposals
            .emplace_back(ProposedDeletions{
                .block_number = n, .round = round, .deletions = {}})
            .deletions;

    for (auto const &[addr, delta] : state_deltas) {
        auto const &account = delta.account.second;
        if (account.has_value()) {
            for (auto const &[key, delta] : delta.storage) {
                if (delta.first != delta.second &&
                    delta.second == bytes32_t{}) {
                    LOG_INFO(
                        "Deleting Storage n={} addr={} storage={} ",
                        n,
                        addr,
                        key);
                    deletions.emplace_back(addr, key);
                }
            }
        }

        if (delta.account.first != account) {
            bool const incarnation =
                account.has_value() && delta.account.first.has_value() &&
                delta.account.first->incarnation != account->incarnation;
            if (incarnation || !account.has_value()) {
                deletions.emplace_back(addr, std::nullopt);
            }
        }
    }
}

void on_finalize(
    monad_statesync_server_context &ctx, uint64_t const block_number,
    uint64_t const round_number)
{
    auto &proposals = ctx.proposals;

    auto winner_it = std::find_if(
        proposals.begin(), proposals.end(), [round_number](auto const &p) {
            return p.round == round_number;
        });

    if (MONAD_UNLIKELY(winner_it == proposals.end())) {
        return;
    }

    MONAD_ASSERT(winner_it->block_number == block_number);

    {
        auto &entry = ctx.deleted[block_number % ctx.deleted.size()];
        std::lock_guard const lock{entry.mutex};
        entry.block_number = block_number;
        entry.deletions = std::move(winner_it->deletions);
    }

    // gc old rounds
    proposals.erase(
        std::remove_if(
            proposals.begin(),
            proposals.end(),
            [round_number](ProposedDeletions const &p) {
                return p.round <= round_number;
            }),
        proposals.end());
}

MONAD_ANONYMOUS_NAMESPACE_END

monad_statesync_server_context::monad_statesync_server_context(TrieDb &rw)
    : rw{rw}
    , ro{nullptr}
{
}

std::optional<Account>
monad_statesync_server_context::read_account(Address const &addr)
{
    return rw.read_account(addr);
}

bytes32_t monad_statesync_server_context::read_storage(
    Address const &addr, Incarnation const incarnation, bytes32_t const &key)
{
    return rw.read_storage(addr, incarnation, key);
}

std::shared_ptr<CodeAnalysis>
monad_statesync_server_context::read_code(bytes32_t const &hash)
{
    return rw.read_code(hash);
}

monad::BlockHeader monad_statesync_server_context::read_eth_header()
{
    return rw.read_eth_header();
}

bytes32_t monad_statesync_server_context::state_root()
{
    return rw.state_root();
}

bytes32_t monad_statesync_server_context::receipts_root()
{
    return rw.receipts_root();
}

bytes32_t monad_statesync_server_context::transactions_root()
{
    return rw.transactions_root();
}

std::optional<bytes32_t> monad_statesync_server_context::withdrawals_root()
{
    return rw.withdrawals_root();
}

void monad_statesync_server_context::set_block_and_round(
    uint64_t const block_number, std::optional<uint64_t> const round_number)
{
    rw.set_block_and_round(block_number, round_number);
}

void monad_statesync_server_context::finalize(
    uint64_t const block_number, uint64_t const round_number)
{
    on_finalize(*this, block_number, round_number);
    rw.finalize(block_number, round_number);
}

void monad_statesync_server_context::update_verified_block(
    uint64_t const block_number)
{
    rw.update_verified_block(block_number);
}

void monad_statesync_server_context::commit(
    StateDeltas const &state_deltas, Code const &code,
    MonadConsensusBlockHeader const &consensus_header,
    std::vector<Receipt> const &receipts,
    std::vector<std::vector<CallFrame>> const &call_frames,
    std::vector<Address> const &senders,
    std::vector<Transaction> const &transactions,
    std::vector<BlockHeader> const &ommers,
    std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    auto &header = consensus_header.execution_inputs;

    on_commit(*this, state_deltas, header.number, consensus_header.round);
    rw.commit(
        state_deltas,
        code,
        consensus_header,
        receipts,
        call_frames,
        senders,
        transactions,
        ommers,
        withdrawals);
}
