#include <category/core/assert.h>
#include <category/core/basic_formatter.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/mpt/db.hpp>
#include <category/statesync/statesync_server_context.hpp>

#include <quill/Quill.h>

#include <algorithm>
#include <cstdint>
#include <mutex>

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

void on_commit(
    monad_statesync_server_context &ctx, StateDeltas const &state_deltas,
    uint64_t const n, bytes32_t const &block_id)
{
    auto &proposals = ctx.proposals;

    auto &deletions =
        proposals
            .emplace_back(ProposedDeletions{
                .block_number = n, .block_id = block_id, .deletions = {}})
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
    bytes32_t const &block_id)
{
    auto &proposals = ctx.proposals;

    auto const it = std::find_if(
        proposals.begin(), proposals.end(), [&block_id](auto const &p) {
            return p.block_id == block_id;
        });

    if (MONAD_UNLIKELY(it == proposals.end())) {
        return;
    }

    MONAD_ASSERT(it->block_number == block_number);

    ctx.deletions.write(block_number, it->deletions);

    // gc proposals of older blocks than finalized block
    proposals.erase(
        std::remove_if(
            proposals.begin(),
            proposals.end(),
            [block_number](ProposedDeletions const &p) {
                return p.block_number <= block_number;
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
    MONAD_ASSERT(entry.block_number == INVALID_BLOCK_NUM);
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
    if (entry.block_number == INVALID_BLOCK_NUM) {
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
    MONAD_ASSERT(entry.block_number == start_block_number_);
    ++start_block_number_;
    std::lock_guard const lock{entry.mutex};
    entry.block_number = INVALID_BLOCK_NUM;
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
    MONAD_ASSERT(block_number != INVALID_BLOCK_NUM);
    MONAD_ASSERT(
        end_block_number_ == INVALID_BLOCK_NUM ||
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
        start_block_number_ = INVALID_BLOCK_NUM;
        MONAD_ASSERT(free_deletions() == MAX_DELETIONS);
    }
    else {
        if (MONAD_UNLIKELY(start_block_number_ == INVALID_BLOCK_NUM)) {
            start_block_number_ = end_block_number_;
        }
        auto const target_idx = end_block_number_ % MAX_ENTRIES;
        clear_entry(target_idx);
        while (free_deletions() < deletions.size()) {
            MONAD_ASSERT(start_block_number_ < end_block_number_);
            clear_entry(start_block_number_ % MAX_ENTRIES);
        }
        set_entry(target_idx, end_block_number_, deletions);
    }
    LOG_INFO(
        "deletions buffer range={} free_deletions={}",
        start_block_number_ == INVALID_BLOCK_NUM
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

monad::vm::SharedIntercode
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

void monad_statesync_server_context::set_block_and_prefix(
    uint64_t const block_number, bytes32_t const &block_id)
{
    rw.set_block_and_prefix(block_number, block_id);
}

void monad_statesync_server_context::finalize(
    uint64_t const block_number, bytes32_t const &block_id)
{
    on_finalize(*this, block_number, block_id);
    rw.finalize(block_number, block_id);
}

void monad_statesync_server_context::update_verified_block(
    uint64_t const block_number)
{
    rw.update_verified_block(block_number);
}

void monad_statesync_server_context::update_voted_metadata(
    uint64_t const block_number, bytes32_t const &block_id)
{
    rw.update_voted_metadata(block_number, block_id);
}

void monad_statesync_server_context::commit(
    StateDeltas const &state_deltas, Code const &code,
    bytes32_t const &block_id, BlockHeader const &header,
    std::vector<Receipt> const &receipts,
    std::vector<std::vector<CallFrame>> const &call_frames,
    std::vector<Address> const &senders,
    std::vector<Transaction> const &transactions,
    std::vector<BlockHeader> const &ommers,
    std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    on_commit(*this, state_deltas, header.number, block_id);
    rw.commit(
        state_deltas,
        code,
        block_id,
        header,
        receipts,
        call_frames,
        senders,
        transactions,
        ommers,
        withdrawals);
}
