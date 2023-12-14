#pragma once

#include <monad/config.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#include <ankerl/unordered_dense.h>

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
    ankerl::unordered_dense::segmented_map<bytes32_t, StorageDelta> storage{};
};

static_assert(sizeof(StateDelta) == 240);
static_assert(alignof(StateDelta) == 8);

using StateDeltas = ankerl::unordered_dense::segmented_map<Address, StateDelta>;

static_assert(sizeof(StateDeltas) == 64);
static_assert(alignof(StateDeltas) == 8);

using Code = ankerl::unordered_dense::segmented_map<bytes32_t, byte_string>;

static_assert(sizeof(Code) == 64);
static_assert(alignof(Code) == 8);

bool can_merge(StateDeltas const &to, StateDeltas const &from);
void merge(StateDeltas &to, StateDeltas const &from);

void merge(Code &to, Code const &from);

MONAD_NAMESPACE_END
