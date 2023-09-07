#include <monad/config.hpp>

#include <monad/db/db.hpp>
#include <monad/db/state_commit.hpp>

#include <monad/state2/block_state.hpp>

MONAD_NAMESPACE_BEGIN

bool can_commit(StateDeltas const &state, Db &db)
{
    bool account_can_commit =
        std::all_of(state.begin(), state.end(), [&](auto const &p) {
            if (p.second.account.first.has_value()) {
                return p.second.account.first == db.read_account(p.first);
            }
            return !db.read_account(p.first).has_value();
        });

    bool storage_can_commit =
        std::all_of(state.begin(), state.end(), [&](auto const &p) {
            return std::all_of(
                p.second.storage.begin(),
                p.second.storage.end(),
                [&](auto const &s) {
                    if (s.second.first == bytes32_t{}) {
                        return true;
                    }

                    return s.second.first ==
                           db.read_storage(p.first, 0u, s.first);
                });
        });

    return (account_can_commit && storage_can_commit);
}

bool can_commit(Code const &code, Db &db)
{
    return std::none_of(code.begin(), code.end(), [&](auto const &a) {
        return !db.read_code(a.first).empty();
    });
}

MONAD_NAMESPACE_END
