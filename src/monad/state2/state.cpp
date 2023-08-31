#include <monad/state2/state.hpp>

#include <monad/core/assert.h>
#include <monad/core/likely.h>

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
            return false;
        }
        if (MONAD_UNLIKELY(!f(it1->second, it2->second))) {
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

bool can_merge(State const &s1, State const &s2)
{
    return subset_f(s1, s2, [](auto const &d1, auto const &d2) {
        if (MONAD_UNLIKELY(d2.account.first != d1.account.second)) {
            return false;
        }
        return subset_f(
            d1.storage, d2.storage, [](auto const &st1, auto const &st2) {
                return st2.first == st1.second;
            });
    });
}

void merge(State &s1, State const &s2)
{
    merge_f(s1, s2, [](auto &d1, auto const &d2) {
        d1.account.second = d2.account.second;
        merge_f(d1.storage, d2.storage, [](auto &st1, auto const &st2) {
            st1.second = st2.second;
        });
    });
}

void merge(Code &c1, Code &c2)
{
    merge_f(c1, c2, [](auto &d1, auto &d2) {
        if (d1.empty())
            d1 = std::move(d2);
        });
}

MONAD_NAMESPACE_END
