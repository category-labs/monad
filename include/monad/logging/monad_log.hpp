#pragma once

#include <monad/logging/config.hpp>

#ifdef DISABLE_LOGGING
    #include <monad/logging/fake_log_macros.hpp>
    #include <monad/logging/fake_logger.hpp>
MONAD_LOG_NAMESPACE_BEGIN
using logger_t = monad::log::FakeEmptyLogger;
MONAD_LOG_NAMESPACE_END
#else
    #include <monad/logging/quill_log_macros.hpp>
    #include <monad/logging/quill_logger.hpp>
MONAD_LOG_NAMESPACE_BEGIN
using logger_t = monad::log::QuillLogger;
MONAD_LOG_NAMESPACE_END
#endif