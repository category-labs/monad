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

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

void on_commit(
    monad_statesync_server_context &ctx, StateDeltas const &state_deltas)
{
    auto const history_length = ctx.rw.get_history_length();
    auto const n = ctx.rw.get_block_number();

    Deleted::accessor it;
    MONAD_ASSERT(ctx.deleted.emplace(it, n, Deleted::mapped_type{}));
    for (auto const &[addr, delta] : state_deltas) {
        auto const &account = delta.account.second;
        std::vector<bytes32_t> storage;
        if (account.has_value()) {
            for (auto const &[key, delta] : delta.storage) {
                if (delta.first != delta.second &&
                    delta.second == bytes32_t{}) {
                    LOG_INFO(
                        "Deleting Storage n={} addr={} storage={} ",
                        n,
                        addr,
                        key);
                    storage.emplace_back(key);
                }
            }
        }

        if (!storage.empty() || delta.account.first != account) {
            bool const incarnation =
                account.has_value() && delta.account.first.has_value() &&
                delta.account.first->incarnation != account->incarnation;
            if (incarnation || !account.has_value()) {
                it->second.emplace_back(addr, std::vector<bytes32_t>{});
            }
            if (!storage.empty()) {
                it->second.emplace_back(addr, std::move(storage));
            }
        }
    }

    uint64_t d = n;
    while (ctx.deleted.size() > history_length) {
        ctx.deleted.erase(d - history_length);
        d--;
    }
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

void monad_statesync_server_context::increment_block_number()
{
    rw.increment_block_number();
}

void monad_statesync_server_context::commit(
    StateDeltas const &state_deltas, Code const &code,
    BlockHeader const &header, std::vector<Receipt> const &receipts,
    std::vector<std::vector<CallFrame>> const &call_frames,
    std::vector<Transaction> const &transactions,
    std::vector<BlockHeader> const &ommers,
    std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    on_commit(*this, state_deltas);
    rw.commit(
        state_deltas,
        code,
        header,
        receipts,
        call_frames,
        transactions,
        ommers,
        withdrawals);
}
