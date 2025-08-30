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
#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/evm/chain.hpp>
#include <category/vm/evm/switch_evm_chain.hpp>

#include <asmjit/x86.h>
#include <evmc/evmc.h>
#include <valgrind/cachegrind.h>

#include <cstdint>
#include <optional>

template <bool instrument>
class InstrumentableCompiler
{
public:
    InstrumentableCompiler(
        asmjit::JitRuntime &rt,
        monad::vm::compiler::native::CompilerConfig const &config)
        : rt_(rt)
        , config_(config)
    {
    }

    template <monad::Traits traits>
    std::shared_ptr<monad::vm::compiler::native::Nativecode> compile(
        monad::vm::compiler::basic_blocks::BasicBlocksIR const &ir,
        InstrumentationDevice const device)
    {
        switch (device) {
        case InstrumentationDevice::Cachegrind:
            return compile<traits, InstrumentationDevice::Cachegrind>(ir);
        case InstrumentationDevice::WallClock:
            return compile<traits, InstrumentationDevice::WallClock>(ir);
        }
        std::unreachable();
    }

    template <monad::Traits traits, InstrumentationDevice device>
    std::shared_ptr<monad::vm::compiler::native::Nativecode>
    compile(monad::vm::compiler::basic_blocks::BasicBlocksIR const &ir)
    {
        if constexpr (instrument) {
            if constexpr (device == InstrumentationDevice::Cachegrind) {
                CACHEGRIND_START_INSTRUMENTATION;
                auto ans =
                    monad::vm::compiler::native::compile_basic_blocks<traits>(
                        rt_, ir, config_);
                CACHEGRIND_STOP_INSTRUMENTATION;
                return ans;
            }
            else {
                timer.start();
                auto ans =
                    monad::vm::compiler::native::compile_basic_blocks<traits>(
                        rt_, ir, config_);
                timer.pause();
                return ans;
            }
        }
        else {
            return monad::vm::compiler::native::compile_basic_blocks<traits>(
                rt_, ir, config_);
        }
    }

private:
    asmjit::JitRuntime &rt_;
    monad::vm::compiler::native::CompilerConfig const &config_;
};
