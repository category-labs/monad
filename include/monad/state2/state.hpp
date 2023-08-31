#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/byte_string.hpp>

#include <ankerl/unordered_dense.h>

#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

template <class T>
using delta_t = std::pair<T const, T>;

using AccountDelta = delta_t<std::optional<Account>>;

static_assert(sizeof(AccountDelta) == 160);
static_assert(alignof(AccountDelta) == 8);

using StorageDelta = delta_t<bytes32_t>;

static_assert(sizeof(StorageDelta) == 64);
static_assert(alignof(StorageDelta) == 1);

struct AccountState
{
    AccountDelta account;
    ankerl::unordered_dense::segmented_map<bytes32_t, StorageDelta> storage;
};

static_assert(sizeof(AccountState) == 224);
static_assert(alignof(AccountState) == 8);

using State = ankerl::unordered_dense::segmented_map<address_t, AccountState>;

static_assert(sizeof(State) == 64);
static_assert(alignof(State) == 8);

using Code =
    ankerl::unordered_dense::segmented_map<bytes32_t, byte_string>;

static_assert(sizeof(Code) == 64);
static_assert(alignof(Code) == 8);

template <class Mutex>
struct BlockState
{
    Mutex mutex;
    State state;
    Code code;
};

bool can_merge(State &to, State const &from);
void merge(State &to, State const &from);

void merge(Code &to, Code &from);

MONAD_NAMESPACE_END
