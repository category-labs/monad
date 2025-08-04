#pragma once

#include <instrumentation_device.hpp>
#include <stopwatch.hpp>

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/core/assert.h>

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

    std::shared_ptr<monad::vm::compiler::native::Nativecode> compile(
        evmc_revision rev,
        monad::vm::compiler::basic_blocks::BasicBlocksIR const &ir,
        InstrumentationDevice const device)
    {
        switch (device) {
        case InstrumentationDevice::Cachegrind:
            return compile<InstrumentationDevice::Cachegrind>(rev, ir);
        case InstrumentationDevice::WallClock:
            return compile<InstrumentationDevice::WallClock>(rev, ir);
        }
        std::unreachable();
    }

    template <InstrumentationDevice device>
    std::shared_ptr<monad::vm::compiler::native::Nativecode> compile(
        evmc_revision rev,
        monad::vm::compiler::basic_blocks::BasicBlocksIR const &ir)
    {
        if constexpr (instrument) {
            if constexpr (device == InstrumentationDevice::Cachegrind) {
                CACHEGRIND_START_INSTRUMENTATION;
                auto ans = monad::vm::compiler::native::compile_basic_blocks(
                    rev, rt_, ir, config_);
                CACHEGRIND_STOP_INSTRUMENTATION;
                return ans;
            }
            else {
                timer.start();
                auto ans = monad::vm::compiler::native::compile_basic_blocks(
                    rev, rt_, ir, config_);
                timer.pause();
                return ans;
            }
        }
        else {
            return monad::vm::compiler::native::compile_basic_blocks(
                rev, rt_, ir, config_);
        }
    }

private:
    asmjit::JitRuntime &rt_;
    monad::vm::compiler::native::CompilerConfig const &config_;
};
