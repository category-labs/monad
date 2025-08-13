// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <gtest/gtest.h>

#include <category/core/config.hpp>
#include <category/core/assert.h>
#include <category/execution/ethereum/trace/event_trace.hpp>
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
