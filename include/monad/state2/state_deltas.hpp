#pragma once

#include <monad/config.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#include <oneapi/tbb/concurrent_unordered_map.h>
#pragma GCC diagnostic pop

#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

template <class T>
using Delta = std::pair<T const, T>;

using AccountDelta = Delta<std::optional<Account>>;

static_assert(sizeof(AccountDelta) == 176);
static_assert(alignof(AccountDelta) == 8);

using StorageDelta = Delta<bytes32_t>;

static_assert(sizeof(StorageDelta) == 64);
static_assert(alignof(StorageDelta) == 1);

struct StateDelta
{
    AccountDelta account;
    oneapi::tbb::concurrent_unordered_map<bytes32_t, StorageDelta> storage{};
};

static_assert(sizeof(StateDelta) == 768);
static_assert(alignof(StateDelta) == 8);

using StateDeltas = oneapi::tbb::concurrent_unordered_map<Address, StateDelta>;

static_assert(sizeof(StateDeltas) == 592);
static_assert(alignof(StateDeltas) == 8);

using Code = oneapi::tbb::concurrent_unordered_map<bytes32_t, byte_string>;

static_assert(sizeof(Code) == 592);
static_assert(alignof(Code) == 8);

MONAD_NAMESPACE_END
