#pragma once

#include <monad/config.hpp>

#include <monad/db/db.hpp>

#include <monad/state/state_changes.hpp>

#include <monad/state2/block_state.hpp>

MONAD_NAMESPACE_BEGIN

bool can_commit(StateDeltas const &state, Db &db);
bool can_commit(Code const &code, Db &db);

template <class Mutex>
bool can_commit(BlockState<Mutex> const &bs, Db &db)
{
    return (can_commit(bs.state, db) && can_commit(bs.code, db));
}

template <class Mutex>
void commit(BlockState<Mutex> &bs, Db &db)
{
    MONAD_DEBUG_ASSERT(can_commit(bs, db));
    state::StateChanges state_changes{};

    for (auto const &[addr, state_delta] : bs.state) {
        if (state_delta.account.first != state_delta.account.second) {
            state_changes.account_changes.emplace_back(
                addr, state_delta.account.second);
        }

        for (auto const &[key, value] : state_delta.storage) {
            if (value.first != value.second) {
                state_changes.storage_changes[addr].emplace_back(
                    key, value.second);
            }
        }
    }

    for (auto &[code_hash, code] : bs.code) {
        state_changes.code_changes.emplace_back(code_hash, std::move(code));
    }

    db.commit(state_changes);

    bs.state.clear();
    bs.code.clear();
}

MONAD_NAMESPACE_END
