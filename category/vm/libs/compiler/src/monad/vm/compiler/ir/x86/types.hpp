#pragma once

#include <monad/vm/runtime/runtime.hpp>

#include <asmjit/x86.h>

#include <functional>

namespace monad::vm::compiler::native
{
    using entrypoint_t = void (*)(runtime::Context *, uint8_t *);

    class Nativecode
    {
    public:
        enum ErrorCode
        {
            NoError,
            Unexpected,
            SizeOutOfBound
        };

        /// If compilation failed, then `entrypoint` is `nullptr`.
        Nativecode(
            asmjit::JitRuntime &asmjit_rt, evmc_revision rev,
            entrypoint_t entry, size_t code_size_estimate)
            : asmjit_rt_{asmjit_rt}
            , revision_{rev}
            , entrypoint_{entry}
            , code_size_estimate_{code_size_estimate}
        {
        }

        Nativecode(Nativecode const &) = delete;
        Nativecode &operator=(Nativecode const &) = delete;

        /// Get native entry point, or `nullptr` if compilation failed.
        entrypoint_t entrypoint() const
        {
            return entrypoint_;
        }

        evmc_revision revision() const
        {
            return revision_;
        }

        size_t code_size_estimate() const
        {
            return entrypoint_ ? code_size_estimate_ : 0;
        }

        size_t code_size_estimate_before_error() const
        {
            return code_size_estimate_;
        }

        ErrorCode error_code() const
        {
            if (entrypoint_) {
                return NoError;
            }
            if (code_size_estimate_ > 0) {
                return SizeOutOfBound;
            }
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
        evmc_revision revision_;
        entrypoint_t entrypoint_;
        size_t code_size_estimate_;
    };

    class Emitter;

    using EmitterHook = std::function<void(Emitter &)>;

    /// Hard upper bound of native code size in bytes, for respecting
    /// size invariants of read-only data section, and to ensure that
    /// relative x86 memory addressing offsets will not overflow. It
    /// is possible to relax this hard upper bound, but native code
    /// size should be smaller than 2GB to avoid overflowing relative
    /// offsets of type `int32_t`.
    constexpr uint64_t code_size_hard_upper_bound = 1 << 30; // 1GB

    struct CompilerConfig
    {
        char const *asm_log_path{};
        bool runtime_debug_trace{};
        bool verbose{};
        uint32_t max_code_size_offset{10 * 1024};
        EmitterHook post_instruction_emit_hook{};
    };
}
