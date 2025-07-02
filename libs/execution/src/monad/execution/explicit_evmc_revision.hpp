#pragma once

#include <evmc/evmc.h>

#define EXPLICIT_EVMC_REVISION(f)                                              \
    template decltype(f<EVMC_FRONTIER>) f<EVMC_FRONTIER>;                      \
    template decltype(f<EVMC_HOMESTEAD>) f<EVMC_HOMESTEAD>;                    \
    template decltype(f<EVMC_TANGERINE_WHISTLE>) f<EVMC_TANGERINE_WHISTLE>;    \
    template decltype(f<EVMC_SPURIOUS_DRAGON>) f<EVMC_SPURIOUS_DRAGON>;        \
    template decltype(f<EVMC_BYZANTIUM>) f<EVMC_BYZANTIUM>;                    \
    template decltype(f<EVMC_CONSTANTINOPLE>) f<EVMC_CONSTANTINOPLE>;          \
    template decltype(f<EVMC_PETERSBURG>) f<EVMC_PETERSBURG>;                  \
    template decltype(f<EVMC_ISTANBUL>) f<EVMC_ISTANBUL>;                      \
    template decltype(f<EVMC_BERLIN>) f<EVMC_BERLIN>;                          \
    template decltype(f<EVMC_LONDON>) f<EVMC_LONDON>;                          \
    template decltype(f<EVMC_PARIS>) f<EVMC_PARIS>;                            \
    template decltype(f<EVMC_SHANGHAI>) f<EVMC_SHANGHAI>;                      \
    template decltype(f<EVMC_CANCUN>) f<EVMC_CANCUN>;                          \
    template decltype(f<EVMC_PRAGUE>) f<EVMC_PRAGUE>;
