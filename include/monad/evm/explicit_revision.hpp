#pragma once

#include <monad/evm/revision.hpp>

#define EXPLICIT_REVISION(f)                                                   \
    template decltype(f<evm::Revision::Frontier>) f<evm::Revision::Frontier>;  \
    template decltype(f<evm::Revision::Homestead>)                             \
        f<evm::Revision::Homestead>;                                           \
    template decltype(f<evm::Revision::TangerineWhistle>)                      \
        f<evm::Revision::TangerineWhistle>;                                    \
    template decltype(f<evm::Revision::SpuriousDragon>)                        \
        f<evm::Revision::SpuriousDragon>;                                      \
    template decltype(f<evm::Revision::Byzantium>)                             \
        f<evm::Revision::Byzantium>;                                           \
    template decltype(f<evm::Revision::Constantinople>)                        \
        f<evm::Revision::Constantinople>;                                      \
    template decltype(f<evm::Revision::Petersburg>)                            \
        f<evm::Revision::Petersburg>;                                          \
    template decltype(f<evm::Revision::Istanbul>) f<evm::Revision::Istanbul>;  \
    template decltype(f<evm::Revision::Berlin>) f<evm::Revision::Berlin>;      \
    template decltype(f<evm::Revision::London>) f<evm::Revision::London>;      \
    template decltype(f<evm::Revision::Paris>) f<evm::Revision::Paris>;        \
    template decltype(f<evm::Revision::Shanghai>) f<evm::Revision::Shanghai>;
