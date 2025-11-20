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
#include <category/vm/evm/traits.hpp>

#ifdef MONAD_COMPILER_LLVM
    #include <category/vm/llvm/llvm.hpp>
#endif

#include <asmjit/x86.h>
#include <evmc/evmc.h>
#include <quill/Quill.h>
#include <valgrind/cachegrind.h>

#include <cstdint>
#include <iostream>
#include <memory>
#include <optional>

using namespace monad;
using namespace monad::vm;
using namespace monad::vm::compiler;

struct LLVMBinary
{
#ifdef MONAD_COMPILER_LLVM
    std::shared_ptr<llvm::LLVMState> llvm_code;
#else
    bool llvm_backend_unavailable{true};
#endif
};

struct CompilerBinary
{
    std::shared_ptr<native::Nativecode> ncode;
};

using Binary = std::variant<CompilerBinary, LLVMBinary>;

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
    Binary compile(
        monad::vm::compiler::basic_blocks::BasicBlocksIR const &ir,
        InstrumentationDevice const device, bool use_llvm)
    {
        switch (device) {
        case InstrumentationDevice::Cachegrind:
            return compile<traits, InstrumentationDevice::Cachegrind>(
                ir, use_llvm);
        case InstrumentationDevice::WallClock:
            return compile<traits, InstrumentationDevice::WallClock>(
                ir, use_llvm);
        }
        std::unreachable();
    }

    template <monad::Traits traits, InstrumentationDevice device>
    Binary compile(
        monad::vm::compiler::basic_blocks::BasicBlocksIR const &ir,
        bool use_llvm)
    {
        if constexpr (instrument) {
            if constexpr (device == InstrumentationDevice::Cachegrind) {
                CACHEGRIND_START_INSTRUMENTATION;
                auto ans = dispatch_compile<traits>(ir, use_llvm);
                CACHEGRIND_STOP_INSTRUMENTATION;
                return ans;
            }
            else {
                timer.start();
                auto ans = dispatch_compile<traits>(ir, use_llvm);
                timer.pause();
                return ans;
            }
        }
        else {
            return dispatch_compile<traits>(ir, use_llvm);
        }
    }

    template <monad::Traits traits>
    Binary dispatch_compile(
        monad::vm::compiler::basic_blocks::BasicBlocksIR const &ir,
        bool use_llvm)
    {
        if (use_llvm) {
#ifdef MONAD_COMPILER_LLVM
            std::shared_ptr<llvm::LLVMState> p =
                llvm::compile_basicblocks_llvm<traits>(ir, "mce_llvm");
            return LLVMBinary{p};
#else
            LOG_ERROR("Unable to compile with LLVM.  LLVM not configured in "
                      "build.  To use the LLVM backend, rebuild with "
                      "-DMONAD_COMPILER_LLVM=On");
            quill::flush();
            abort();
#endif
        }
        std::shared_ptr<monad::vm::compiler::native::Nativecode> nc =
            monad::vm::compiler::native::compile_basic_blocks<traits>(
                rt_, ir, config_);
        if (!nc->entrypoint()) {
            LOG_ERROR("Compilation failed.");
            quill::flush();
            abort();
        }

        return CompilerBinary{nc};
    }

private:
    asmjit::JitRuntime &rt_;
    monad::vm::compiler::native::CompilerConfig const &config_;
};
