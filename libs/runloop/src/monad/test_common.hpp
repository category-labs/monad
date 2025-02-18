#pragma once

#include "monad/async/cpp_helpers.hpp"

using namespace monad::async;
using namespace monad::context;
#define CHECK_RESULT2(unique, ...)                                             \
    {                                                                          \
        auto _r_ = to_result(__VA_ARGS__);                                     \
        if (!_r_ && _r_.assume_error() != errc::stream_timeout) {              \
            _r_.value();                                                       \
        }                                                                      \
    }
#define CHECK_RESULT(...) CHECK_RESULT2(MONAD_ASYNC_UNIQUE_NAME, __VA_ARGS__)
