#pragma once

#include <evmc/evmc.h>
#include <monad/config.hpp>
#include <monad/core/assert.h>

#include <utility>

#define DECL_REV(f)                                                            \
    template <evmc_revision rev>                                               \
    struct rev_##f                                                             \
    {                                                                          \
        auto operator()(auto &&...args)                                        \
        {                                                                      \
            return f<rev>(std::forward<decltype(args)>(args)...);              \
        }                                                                      \
    };

MONAD_NAMESPACE_BEGIN

template <template <evmc_revision> class F, class... Args>
constexpr auto invoke_rev(evmc_revision const rev, Args &&...args)
{
    switch (rev) {
    case EVMC_SHANGHAI:
        return F<EVMC_SHANGHAI>{}(std::forward<Args>(args)...);
    case EVMC_PARIS:
        return F<EVMC_PARIS>{}(std::forward<Args>(args)...);
    case EVMC_LONDON:
        return F<EVMC_LONDON>{}(std::forward<Args>(args)...);
    case EVMC_BERLIN:
        return F<EVMC_BERLIN>{}(std::forward<Args>(args)...);
    case EVMC_ISTANBUL:
        return F<EVMC_ISTANBUL>{}(std::forward<Args>(args)...);
    case EVMC_PETERSBURG:
    case EVMC_CONSTANTINOPLE:
        return F<EVMC_PETERSBURG>{}(std::forward<Args>(args)...);
    case EVMC_BYZANTIUM:
        return F<EVMC_BYZANTIUM>{}(std::forward<Args>(args)...);
    case EVMC_SPURIOUS_DRAGON:
        return F<EVMC_SPURIOUS_DRAGON>{}(std::forward<Args>(args)...);
    case EVMC_TANGERINE_WHISTLE:
        return F<EVMC_TANGERINE_WHISTLE>{}(std::forward<Args>(args)...);
    case EVMC_HOMESTEAD:
        return F<EVMC_HOMESTEAD>{}(std::forward<Args>(args)...);
    case EVMC_FRONTIER:
        return F<EVMC_FRONTIER>{}(std::forward<Args>(args)...);
    default:
        MONAD_ASSERT(false);
        break;
    }
}

MONAD_NAMESPACE_END
