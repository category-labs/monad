// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/vm/runtime/engine_timer.hpp>

#include <gtest/gtest.h>

#include <chrono>
#include <thread>

using namespace monad::vm::runtime;
using namespace std::chrono_literals;

TEST(EngineTimer, ChargesTimeToCurrentSection)
{
    EngineTimer timer;

    timer.enter(EngineTimer::Engine);
    std::this_thread::sleep_for(2ms);
    auto const prev = timer.enter(EngineTimer::Keccak);
    std::this_thread::sleep_for(1ms);
    timer.enter(EngineTimer::Host);
    auto const engine = timer.elapsed(EngineTimer::Engine);
    auto const keccak = timer.elapsed(EngineTimer::Keccak);
    std::this_thread::sleep_for(1ms);
    timer.enter(prev);

    EXPECT_EQ(prev, EngineTimer::Engine);
    EXPECT_GE(engine, 2ms);
    EXPECT_GE(keccak, 1ms);
    EXPECT_EQ(timer.elapsed(EngineTimer::Engine), engine);
    EXPECT_EQ(timer.elapsed(EngineTimer::Keccak), keccak);
    EXPECT_EQ(timer.elapsed(EngineTimer::Host), 0ns);
}
