#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/likely.h>
#include <monad/db/trie_db.hpp>
#include <monad/mpt/db.hpp>
#include <monad/statesync/statesync_server_context.hpp>

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

#include <algorithm>
#include <cstdint>

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

void on_commit(
    monad_statesync_server_context &ctx, StateDeltas const &state_deltas)
{
    MONAD_ASSERT(ctx.deleted.size() <= ctx.rw.get_history_length());
    auto const n = ctx.rw.get_block_number();

    Deleted::accessor it;
    MONAD_ASSERT(ctx.deleted.emplace(it, n, Deleted::mapped_type{}));
    for (auto const &[addr, delta] : state_deltas) {
        auto const &account = delta.account.second;
        std::vector<byte_string> storage;
        if (account.has_value()) {
            for (auto const &[key, delta] : delta.storage) {
                if (delta.first != delta.second &&
                    delta.second == bytes32_t{}) {
                    auto const akey = keccak256(addr.bytes);
                    auto const skey = keccak256(key.bytes);
                    LOG_INFO(
                        "Deleting Storage n={} {} ",
                        n,
                        fmt::format(
                            "akey=0x{:02x} skey=0x{:02x}",
                            fmt::join(std::as_bytes(std::span(akey.bytes)), ""),
                            fmt::join(
                                std::as_bytes(std::span(skey.bytes)), "")));
                    storage.emplace_back(skey.bytes, sizeof(skey));
                }
            }
        }

        if (!storage.empty() || delta.account.first != account) {
            bool const incarnation =
                account.has_value() && delta.account.first.has_value() &&
                delta.account.first->incarnation != account->incarnation;
            auto const key = keccak256(addr.bytes);
            if (incarnation || !account.has_value()) {
                it->second.emplace_back(
                    to_byte_string_view(key.bytes), std::vector<byte_string>{});
            }
            if (!storage.empty()) {
                it->second.emplace_back(
                    to_byte_string_view(key.bytes), std::move(storage));
            }
        }
    }

    if (MONAD_LIKELY(n >= ctx.rw.get_history_length())) {
        ctx.deleted.erase(n - ctx.rw.get_history_length());
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

void monad_statesync_server_context::increment_block_number()
{
    rw.increment_block_number();
}

void monad_statesync_server_context::commit(
    StateDeltas const &state_deltas, Code const &code,
    std::vector<Receipt> const &receipts)
{
    on_commit(*this, state_deltas);
    rw.commit(state_deltas, code, receipts);
}
