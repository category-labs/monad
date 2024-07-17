#pragma once

#include <gtest/gtest.h>

#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/execution/trace/event_trace.hpp>
#include <monad/test/config.hpp>

#include <quill/Quill.h>

MONAD_NAMESPACE_BEGIN

quill::Logger *event_tracer = nullptr;

MONAD_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

class Environment : public ::testing::Environment
{
public:
    void SetUp() override
    {
        quill::start();
#ifdef ENABLE_EVENT_TRACING
        event_tracer =
            quill::create_logger("event_trace", quill::null_handler());
#endif
    }
};

MONAD_TEST_NAMESPACE_END
