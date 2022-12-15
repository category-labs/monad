#pragma once

#include <iostream>
#include <monad/core/assert.h>

#define MONAD_ROCKS_ASSERT(res)                                                \
    if (MONAD_UNLIKELY(!res.ok())) {                                           \
        std::cerr << "Failed with " << res.ToString() << std::endl;            \
        MONAD_ASSERT(res.ok());                                                \
    }
