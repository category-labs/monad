#pragma once

#include "monad/async/cpp_helpers.hpp"

using namespace monad::async;
#define CHECK_RESULT2(unique, ...)                                             \
    {                                                                          \
        to_result(__VA_ARGS__).value();                                        \
    }
#define CHECK_RESULT(...) CHECK_RESULT2(MONAD_ASYNC_UNIQUE_NAME, __VA_ARGS__)
