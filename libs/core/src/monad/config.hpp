#pragma once

#include "config.h"

#include <bit>
#include <climits>

#define MONAD_NAMESPACE_BEGIN                                                  \
    namespace monad                                                            \
    {

#define MONAD_NAMESPACE_END }

#define MONAD_NAMESPACE ::monad

static_assert(CHAR_BIT == 8);

static_assert(
    std::endian::native == std::endian::big ||
    std::endian::native == std::endian::little);
