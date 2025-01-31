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

    auto const it = std::find_if(
        proposals.begin(), proposals.end(), [round_number](auto const &p) {
            return p.round == round_number;
        });

    if (MONAD_UNLIKELY(it == proposals.end())) {
        return;
    }

    MONAD_ASSERT(it->block_number == block_number);

    ctx.deletions.write(block_number, it->deletions);

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

MONAD_NAMESPACE_BEGIN

void FinalizedDeletions::set_entry(
    uint64_t const i, uint64_t const block_number,
    std::vector<Deletion> const &deletions)
{
    auto &entry = entries_[i];
    std::lock_guard const lock{entry.mutex};
    MONAD_ASSERT(entry.block_number == INVALID_BLOCK_ID);
    entry.block_number = block_number;
    entry.idx = free_start_;
    entry.size = deletions.size();
    for (auto const &deletion : deletions) {
        deletions_[free_start_++ % MAX_DELETIONS] = deletion;
    }
    LOG_INFO(
        "deletions buffer write i={} "
        "FinalizedDeletionsEntry{{block_number={} idx={} "
        "size={}}}",
        i,
        entry.block_number,
        entry.idx,
        entry.size);
}

void FinalizedDeletions::clear_entry(uint64_t const i)
{
    auto &entry = entries_[i];
    if (entry.block_number == INVALID_BLOCK_ID) {
        return;
    }
    LOG_INFO(
        "deletions buffer clear i={} "
        "FinalizedDeletionsEntry{{block_number={} idx={} "
        "size={}}}",
        i,
        entry.block_number,
        entry.idx,
        entry.size);
    free_end_ += entry.size;
    std::lock_guard const lock{entry.mutex};
    entry.block_number = INVALID_BLOCK_ID;
    entry.idx = 0;
    entry.size = 0;
}

bool FinalizedDeletions::for_each(
    uint64_t const block_number, std::function<void(Deletion const &)> const fn)
{
    auto &entry = entries_[block_number % MAX_ENTRIES];
    std::lock_guard const lock{entry.mutex};
    if (entry.block_number != block_number) {
        return false;
    }
    for (size_t i = 0; i < entry.size; ++i) {
        auto const idx = (entry.idx + i) % MAX_DELETIONS;
        fn(deletions_[idx]);
    }
    return true;
}

void FinalizedDeletions::write(
    uint64_t const block_number, std::vector<Deletion> const &deletions)
{
    MONAD_ASSERT(block_number != INVALID_BLOCK_ID);
    MONAD_ASSERT(
        end_block_number_ == INVALID_BLOCK_ID ||
        (end_block_number_ + 1) == block_number);

    auto const free_deletions = [this] { return free_end_ - free_start_; };

    end_block_number_ = block_number;

    if (MONAD_UNLIKELY(deletions.size() > MAX_DELETIONS)) { // blow away
        LOG_WARNING(
            "dropping deletions due to exessive size block_number={} size={}",
            block_number,
            deletions.size());
        for (uint64_t i = 0; i < MAX_ENTRIES; ++i) {
            clear_entry(i);
        }
        start_block_number_ = INVALID_BLOCK_ID;
        MONAD_ASSERT(free_deletions() == MAX_DELETIONS);
    }
    else {
        if (MONAD_UNLIKELY(start_block_number_ == INVALID_BLOCK_ID)) {
            start_block_number_ = end_block_number_;
        }
        auto const target_idx = end_block_number_ % MAX_ENTRIES;
        clear_entry(target_idx);
        while (free_deletions() < deletions.size()) {
            MONAD_ASSERT(start_block_number_ < end_block_number_);
            clear_entry(start_block_number_ % MAX_ENTRIES);
            ++start_block_number_;
        }
        set_entry(target_idx, end_block_number_, deletions);
    }
    LOG_INFO(
        "deletions buffer range={} free_deletions={}",
        start_block_number_ == INVALID_BLOCK_ID
            ? "EMPTY"
            : fmt::format("[{}, {}]", start_block_number_, end_block_number_),
        free_deletions());
}

MONAD_NAMESPACE_END

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
    std::vector<Transaction> const &transactions,
    std::vector<ExecutionResult> const &txn_exec_results,
    std::vector<BlockHeader> const &ommers,
    std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    auto &header = consensus_header.execution_inputs;

    on_commit(*this, state_deltas, header.number, consensus_header.round);
    rw.commit(
        state_deltas,
        code,
        consensus_header,
        transactions,
        txn_exec_results,
        ommers,
        withdrawals);
}
