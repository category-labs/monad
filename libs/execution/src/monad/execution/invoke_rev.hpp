#pragma once

#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/execution/explicit_evmc_revision.hpp>

#include <evmc/evmc.h>

#include <utility>

MONAD_NAMESPACE_BEGIN

template <template <evmc_revision> class F, class... Args>
constexpr auto invoke_rev(evmc_revision const rev, Args &&...args)
{
#define ON_EVMC_REVISION_INVOKE(f, rev)                                        \
    case rev:                                                                  \
        return f<rev>{}(std::forward<Args>(args)...);

    switch (rev) {
        FOR_EACH_EVMC_REVISION(F, ON_EVMC_REVISION_INVOKE)
    default:
        MONAD_ASSERT(false);
        break;
    }
#undef ON_EVMC_REVISION_INVOKE
}

MONAD_NAMESPACE_END
