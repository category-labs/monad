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

#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/bin.hpp>
#include <category/vm/runtime/runtime.hpp>

#include <asmjit/x86.h>

#include <functional>
#include <optional>
#include <variant>

namespace monad::vm::compiler::native
{
    /// Native code size should be smaller than 2GB to avoid overflowing
    /// relative offsets of type `int32_t`.
    using native_code_size_t = runtime::Bin<26>;
    using entrypoint_t = void (*)(runtime::Context *, uint8_t *);

    class Nativecode
    {
    public:
        struct SizeEstimateOutOfBounds
        {
            size_t size_estimate;
        };

        enum ErrorCode
        {
            NoError,
            Unexpected,
            SizeOutOfBound
        };

        using CodeSizeEstimate =
            std::variant<std::monostate, size_t, native_code_size_t>;

        /// If compilation failed, then `entrypoint` is `nullptr`.
        Nativecode(
            asmjit::JitRuntime &asmjit_rt, uint64_t chain_id,
            entrypoint_t entry, CodeSizeEstimate code_size_estimate)
            : asmjit_rt_{asmjit_rt}
            , chain_id_{chain_id}
            , entrypoint_{entry}
            , code_size_estimate_{code_size_estimate}
        {
            MONAD_VM_DEBUG_ASSERT(
                !!entrypoint_ ==
                std::holds_alternative<native_code_size_t>(code_size_estimate));
        }

        Nativecode(Nativecode const &) = delete;
        Nativecode &operator=(Nativecode const &) = delete;

        /// Get native entry point, or `nullptr` if compilation failed.
        entrypoint_t entrypoint() const
        {
            return entrypoint_;
        }

        uint64_t chain_id() const noexcept
        {
            return chain_id_;
        }

        native_code_size_t code_size_estimate() const
        {
            return std::holds_alternative<native_code_size_t>(
                       code_size_estimate_)
                       ? std::get<native_code_size_t>(code_size_estimate_)
                       : native_code_size_t{};
        }

        size_t code_size_estimate_before_error() const
        {
            if (std::holds_alternative<size_t>(code_size_estimate_)) {
                return std::get<size_t>(code_size_estimate_);
            }
            if (std::holds_alternative<native_code_size_t>(
                    code_size_estimate_)) {
                return *std::get<native_code_size_t>(code_size_estimate_);
            }
            return 0;
        }

        ErrorCode error_code() const
        {
            if (entrypoint_) {
                MONAD_VM_DEBUG_ASSERT(
                    std::holds_alternative<native_code_size_t>(
                        code_size_estimate_));
                return NoError;
            }
            if (std::holds_alternative<size_t>(code_size_estimate_)) {
                return SizeOutOfBound;
            }
            MONAD_VM_DEBUG_ASSERT(
                std::holds_alternative<std::monostate>(code_size_estimate_));
            return Unexpected;
        }

        ~Nativecode()
        {
            if (entrypoint_) {
                asmjit_rt_.release(entrypoint_);
            }
        }

    private:
        asmjit::JitRuntime &asmjit_rt_;
        uint64_t chain_id_;
        entrypoint_t entrypoint_;
        CodeSizeEstimate code_size_estimate_;
    };

    class Emitter;

    using EmitterHook = std::function<void(Emitter &)>;

    struct CompilerConfig
    {
        char const *asm_log_path{};
        bool runtime_debug_trace{};
        interpreter::code_size_t max_code_size_offset =
            monad::vm::runtime::bin<10 * 1024>;
        EmitterHook post_instruction_emit_hook{};
    };
}
