#include <monad/config.hpp>

#include <monad/state2/state_deltas.hpp>

#include <monad/core/assert.h>
#include <monad/core/likely.h>

MONAD_NAMESPACE_BEGIN

bool can_merge(StateDelta const &to, StateDelta const &from)
{
    if (MONAD_UNLIKELY(from.account.first != to.account.second)) {
        return false;
    }
    for (auto it = from.storage.begin(); it != from.storage.end(); ++it) {
        auto const it2 = to.storage.find(it->first);
        if (MONAD_UNLIKELY(it2 == to.storage.end())) {
            return false;
        }
        if (MONAD_UNLIKELY(it->second.first != it2->second.second)) {
            return false;
        }
    }
    return true;
}

void merge(StateDelta &to, StateDelta const &from)
{
    to.account.second = from.account.second;
    if (MONAD_LIKELY(from.account.second.has_value())) {
        for (auto it = from.storage.begin(); it != from.storage.end(); ++it) {
            auto const it2 = to.storage.find(it->first);
            MONAD_ASSERT(it2 != to.storage.end());
            it2->second.second = it->second.second;
        }
    }
    else {
        to.storage.clear();
    }
}

bool can_merge(StateDeltas const &to, StateDeltas const &from)
{
    for (auto it = from.begin(); it != from.end(); ++it) {
        auto const it2 = to.find(it->first);
        MONAD_ASSERT(it2 != to.end());
        if (MONAD_UNLIKELY(!can_merge(it2->second, it->second))) {
            return false;
        }
    }
    return true;
}

void merge(StateDeltas &to, StateDeltas const &from)
{
    for (auto it = from.begin(); it != from.end(); ++it) {
        auto const it2 = to.find(it->first);
        MONAD_ASSERT(it2 != to.end());
        merge(it2->second, it->second);
    }
}

void merge(Code &to, Code const &from)
{
    for (auto it = from.begin(); it != from.end(); ++it) {
        auto const it2 = to.find(it->first);
        MONAD_ASSERT(it2 != to.end());
        if (it2->second.empty()) {
            it2->second = it->second;
        }
    }
}

MONAD_NAMESPACE_END
