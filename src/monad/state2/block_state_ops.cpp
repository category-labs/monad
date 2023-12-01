#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/state2/block_state.hpp>
#include <monad/state2/block_state_ops.hpp>
#include <monad/state2/state_deltas.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

std::optional<Account> &read_account(
    Address const &address, StateDeltas &state, BlockState &block_state)
{
    // state
    {
        auto const it = state.find(address);
        if (MONAD_LIKELY(it != state.end())) {
            return it->second.account.second;
        }
    }
    auto const result = block_state.read_account(address);
    auto const [it, _] = state.try_emplace(
        address, StateDelta{.account = {result, result}, .storage = {}});
    return it->second.account.second;
}

Delta<bytes32_t> &read_storage_delta(
    Address const &address, uint64_t const /*incarnation*/,
    bytes32_t const &location, StateDeltas &state, BlockState &block_state)
{
    // state
    auto const it = state.find(address);
    MONAD_ASSERT(it != state.end());
    auto &storage = it->second.storage;
    {
        auto const it2 = storage.find(location);
        if (MONAD_LIKELY(it2 != storage.end())) {
            return it2->second;
        }
    }
    auto const result = block_state.read_storage(address, 0, location);
    auto const [it2, _] = storage.try_emplace(location, result, result);
    return it2->second;
}

byte_string &
read_code(bytes32_t const &hash, Code &code, BlockState &block_state)
{
    // code
    {
        auto const it = code.find(hash);
        if (MONAD_LIKELY(it != code.end())) {
            return it->second;
        }
    }
    auto const result = block_state.read_code(hash);
    auto const [it, _] = code.try_emplace(hash, result);
    return it->second;
}

MONAD_NAMESPACE_END
