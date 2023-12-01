#pragma once

#include <monad/config.hpp>
#include <monad/db/db.hpp>
#include <monad/state2/state_deltas.hpp>

#include <shared_mutex>

MONAD_NAMESPACE_BEGIN

class BlockState final
{
    using Mutex = std::shared_mutex;
    using SharedLock = std::shared_lock<Mutex>;
    using LockGuard = std::lock_guard<Mutex>;

    Db &db_;
    Mutex mutex_;
    StateDeltas state_;
    Code code_;

public:
    BlockState(Db &);

    std::optional<Account> read_account(Address const &);

    bytes32_t read_storage(
        Address const &, uint64_t incarnation, bytes32_t const &location);

    byte_string read_code(bytes32_t const &hash);

    bool can_merge(StateDeltas const &);

    void merge(StateDeltas const &);

    void merge(Code const &);

    void commit();
};

MONAD_NAMESPACE_END
