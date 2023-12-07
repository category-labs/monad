#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/state2/state.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/state2/state_deltas_fmt.hpp>

#include <quill/detail/LogMacros.h>

#include <optional>

MONAD_NAMESPACE_BEGIN

std::optional<Account> &State::read_account(Address const &address)
{
    // state
    {
        auto const it = state_.find(address);
        if (MONAD_LIKELY(it != state_.end())) {
            return it->second.account.second;
        }
    }
    auto const result = block_state_.read_account(address);
    auto const [it, _] = state_.try_emplace(
        address, StateDelta{.account = {result, result}, .storage = {}});
    return it->second.account.second;
}

Delta<bytes32_t> &
State::read_storage_delta(Address const &address, bytes32_t const &location)
{
    // state
    auto const it = state_.find(address);
    MONAD_ASSERT(it != state_.end());
    auto &storage = it->second.storage;
    {
        auto const it2 = storage.find(location);
        if (MONAD_LIKELY(it2 != storage.end())) {
            return it2->second;
        }
    }
    auto const result = block_state_.read_storage(address, 0, location);
    auto const [it2, _] = storage.try_emplace(location, result, result);
    return it2->second;
}

byte_string &State::read_code(bytes32_t const &hash)
{
    // code
    {
        auto const it = code_.find(hash);
        if (MONAD_LIKELY(it != code_.end())) {
            return it->second;
        }
    }
    auto const result = block_state_.read_code(hash);
    auto const [it, _] = code_.try_emplace(hash, result);
    return it->second;
}

void State::log_debug() const
{
    LOG_DEBUG("State Deltas: {}", state_);
    LOG_DEBUG("Code Deltas: {}", code_);
}

MONAD_NAMESPACE_END
