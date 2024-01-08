#include <monad/config.hpp>

#include <monad/state2/state_deltas.hpp>

#include <monad/core/assert.h>
#include <monad/core/likely.h>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <monad/core/address_fmt.hpp>
#include <monad/core/bytes_fmt.hpp>
#include <monad/state2/state_deltas_fmt.hpp>

MONAD_NAMESPACE_BEGIN

/**
 * returns true if for all (x2, y2) in m2,
 *   there is (x1, y1) in m1 such that x1 = x2 and f(y1, y2) is true
 * returns false otherwise
 */
bool subset_f(auto const &m1, auto const &m2, auto &&f)
{
    for (auto it2 = m2.begin(); it2 != m2.end(); ++it2) {
        auto const it1 = m1.find(it2->first);
        if (MONAD_UNLIKELY(it1 == m1.end())) {
            LOG_INFO("it2 first: {}", it2->first);
            quill::flush();
            return false;
        }
        if (MONAD_UNLIKELY(!f(it1->second, it2->second))) {
            LOG_INFO("it2->first: {}", it2->first);
            LOG_INFO("it1->second: {}", it1->second);
            LOG_INFO("it2->second: {}", it2->second);
            quill::flush();
            return false;
        }
    }
    return true;
}

/**
 * merge m2 into m1 using function f
 *   for each (x2, y2) in m2,
 *   find (x1, y1) in m1 such that x1 = x2 and execute f(y1, y2)
 */
void merge_f(auto &m1, auto const &m2, auto &&f)
{
    for (auto it2 = m2.begin(); it2 != m2.end(); ++it2) {
        auto const it1 = m1.find(it2->first);
        MONAD_DEBUG_ASSERT(it1 != m1.end());
        f(it1->second, it2->second);
    }
}

void special_merge_f(auto &m1, auto const &m2, auto &&f)
{
    for (auto it1 = m1.begin(); it1 != m1.end(); ++it1) {
        auto const it2 = m2.find(it1->first);
        if (it2 == m2.end()) {
            it1->second.second = bytes32_t{};
        }
        else {
            f(it1->second, it2->second);
        }
    }
}

bool can_merge(StateDeltas const &to, StateDeltas const &from)
{
    return subset_f(to, from, [](auto const &d1, auto const &d2) {
        if (MONAD_UNLIKELY(d2.account.first != d1.account.second)) {
            return false;
        }
        return (d2.account.second.has_value() &&
                d2.account.second->incarnation == 2) ||
               subset_f(
                   d1.storage,
                   d2.storage,
                   [](auto const &st1, auto const &st2) {
                       return st2.first == st1.second;
                   });
    });
}

void merge(StateDeltas &to, StateDeltas const &from)
{
    merge_f(to, from, [](auto &d1, auto const &d2) {
        d1.account.second = d2.account.second;
        if (MONAD_UNLIKELY(
                d2.account.second.has_value() &&
                d2.account.second->incarnation == 2)) {
            d1.account.second->incarnation = 1;
            special_merge_f(
                d1.storage, d2.storage, [](auto &st1, auto const &st2) {
                    st1.second = st2.second;
                });
        }
        else if (d2.account.second.has_value()) {
            merge_f(d1.storage, d2.storage, [](auto &st1, auto const &st2) {
                st1.second = st2.second;
            });
        }
        else {
            d1.storage.clear();
        }
    });
}

void merge(Code &to, Code const &from)
{
    merge_f(to, from, [](auto &d1, auto &d2) {
        if (d1.empty()) {
            d1 = d2;
        }
    });
}

MONAD_NAMESPACE_END
