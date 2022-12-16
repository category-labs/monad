#pragma once

#include <monad/config.hpp>

#include <silkworm/types/account.hpp>

MONAD_NAMESPACE_BEGIN

using Account = ::silkworm::Account;

static_assert(sizeof(Account) == 80);
static_assert(alignof(Account) == 8);

MONAD_NAMESPACE_END
