#pragma once

#include <instrumentation_device.hpp>
#include <stopwatch.hpp>

#include <monad/vm/compiler/ir/basic_blocks.hpp>
#include <monad/vm/core/assert.h>

#include <evmc/evmc.h>
#include <valgrind/cachegrind.h>

#include <cstdint>
#include <vector>

template <bool instrument>
class InstrumentableParser
{
public:
    template <evmc_revision Rev>
    std::optional<monad::vm::compiler::basic_blocks::BasicBlocksIR>
    parse(std::vector<uint8_t> const &code, InstrumentationDevice const device)
    {
        switch (device) {
        case InstrumentationDevice::Cachegrind:
            return parse<Rev, InstrumentationDevice::Cachegrind>(code);
        case InstrumentationDevice::WallClock:
            return parse<Rev, InstrumentationDevice::WallClock>(code);
        }
        std::unreachable();
    }

    template <evmc_revision Rev, InstrumentationDevice device>
    std::optional<monad::vm::compiler::basic_blocks::BasicBlocksIR>
    parse(std::vector<uint8_t> const &code)
    {
        if constexpr (instrument) {
            if constexpr (device == InstrumentationDevice::Cachegrind) {
                CACHEGRIND_START_INSTRUMENTATION;
                auto ir = monad::vm::compiler::basic_blocks::BasicBlocksIR(
                    monad::vm::compiler::basic_blocks::make_ir<Rev>(code));
                CACHEGRIND_STOP_INSTRUMENTATION;
                return ir;
            }
            else {
                timer.start();
                auto ir = monad::vm::compiler::basic_blocks::BasicBlocksIR(
                    monad::vm::compiler::basic_blocks::make_ir<Rev>(code));
                timer.pause();
                return ir;
            }
        }
        else {
            return monad::vm::compiler::basic_blocks::BasicBlocksIR(
                monad::vm::compiler::basic_blocks::make_ir<Rev>(code));
        }
    }
};
