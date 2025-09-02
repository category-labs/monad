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

#include <instrumentation_device.hpp>
#include <stopwatch.hpp>

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>
#include <valgrind/cachegrind.h>

#include <cstdint>
#include <vector>

template <bool instrument>
class InstrumentableParser
{
public:
    template <monad::Traits traits>
    std::optional<monad::vm::compiler::basic_blocks::BasicBlocksIR>
    parse(std::vector<uint8_t> const &code, InstrumentationDevice const device)
    {
        switch (device) {
        case InstrumentationDevice::Cachegrind:
            return parse<traits, InstrumentationDevice::Cachegrind>(code);
        case InstrumentationDevice::WallClock:
            return parse<traits, InstrumentationDevice::WallClock>(code);
        }
        std::unreachable();
    }

    template <monad::Traits traits, InstrumentationDevice device>
    std::optional<monad::vm::compiler::basic_blocks::BasicBlocksIR>
    parse(std::vector<uint8_t> const &code)
    {
        if constexpr (instrument) {
            if constexpr (device == InstrumentationDevice::Cachegrind) {
                CACHEGRIND_START_INSTRUMENTATION;
                auto ir = monad::vm::compiler::basic_blocks::BasicBlocksIR(
                    monad::vm::compiler::basic_blocks::unsafe_make_ir<traits>(
                        code));
                CACHEGRIND_STOP_INSTRUMENTATION;
                return ir;
            }
            else {
                timer.start();
                auto ir = monad::vm::compiler::basic_blocks::BasicBlocksIR(
                    monad::vm::compiler::basic_blocks::unsafe_make_ir<traits>(
                        code));
                timer.pause();
                return ir;
            }
        }
        else {
            return monad::vm::compiler::basic_blocks::BasicBlocksIR(
                monad::vm::compiler::basic_blocks::unsafe_make_ir<traits>(
                    code));
        }
    }
};
