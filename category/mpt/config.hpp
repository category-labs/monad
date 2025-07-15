#pragma once

#include <category/core/config.hpp>

#define MONAD_MPT_NAMESPACE_BEGIN                                              \
    MONAD_NAMESPACE_BEGIN namespace mpt                                        \
    {

#define MONAD_MPT_NAMESPACE_END                                                \
    }                                                                          \
    MONAD_NAMESPACE_END

#define MONAD_MPT_NAMESPACE ::monad::mpt

MONAD_MPT_NAMESPACE_BEGIN

static constexpr unsigned EMPTY_STRING_RLP_LENGTH = 1;
static constexpr unsigned char RLP_EMPTY_STRING = 0x80;

MONAD_MPT_NAMESPACE_END