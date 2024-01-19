#pragma once

#include <monad/config.hpp>
#include <monad/db/db.hpp>
#include <monad/state2/state_deltas.hpp>

#include <shared_mutex>

MONAD_NAMESPACE_BEGIN

class State;

class BlockState final
{
    using Mutex = std::shared_mutex;
    using ReadLock = std::shared_lock<Mutex>;
    using WriteLock = std::lock_guard<Mutex>;

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

    bool can_merge(State const &);

    void merge(State const &);

    void commit();

    void log_debug();
};

MONAD_NAMESPACE_END
