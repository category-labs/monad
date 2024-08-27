#pragma once

#include <evmc/evmc.h>

#define FOR_EACH_EVMC_REVISION(f, ON_EVMC_REVISION)                            \
    ON_EVMC_REVISION(f, EVMC_FRONTIER);                                        \
    ON_EVMC_REVISION(f, EVMC_HOMESTEAD);                                       \
    ON_EVMC_REVISION(f, EVMC_TANGERINE_WHISTLE);                               \
    ON_EVMC_REVISION(f, EVMC_SPURIOUS_DRAGON);                                 \
    ON_EVMC_REVISION(f, EVMC_BYZANTIUM);                                       \
    ON_EVMC_REVISION(f, EVMC_CONSTANTINOPLE);                                  \
    ON_EVMC_REVISION(f, EVMC_PETERSBURG);                                      \
    ON_EVMC_REVISION(f, EVMC_ISTANBUL);                                        \
    ON_EVMC_REVISION(f, EVMC_BERLIN);                                          \
    ON_EVMC_REVISION(f, EVMC_LONDON);                                          \
    ON_EVMC_REVISION(f, EVMC_PARIS);                                           \
    ON_EVMC_REVISION(f, EVMC_SHANGHAI);

#define EXPLICIT_EVMC_REVISION_F(f, rev) template decltype(f<rev>) f<rev>
#define EXPLICIT_EVMC_REVISION_S(f, rev) template struct f<rev>

#define EXPLICIT_EVMC_REVISION(f)                                              \
    FOR_EACH_EVMC_REVISION(f, EXPLICIT_EVMC_REVISION_F)

#define EXPLICIT_EVMC_REVISION_STRUCT(s)                                       \
    FOR_EACH_EVMC_REVISION(s, EXPLICIT_EVMC_REVISION_S)
