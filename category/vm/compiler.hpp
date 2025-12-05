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

#include <category/vm/code.hpp>
#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/utils/debug.hpp>
#include <category/vm/utils/log_utils.hpp>
#include <category/vm/varcode_cache.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <tbb/concurrent_hash_map.h>
#include <tbb/concurrent_queue.h>

#include <asmjit/x86.h>

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <thread>

namespace monad::vm
{
    using CompilerConfig = compiler::native::CompilerConfig;

    struct CompilerStats
    {
        utils::EuclidMean<uint64_t> avg_native_code_size_;
        utils::EuclidMean<uint64_t> avg_compiled_bytecode_size_;
        utils::GeoMean<double> avg_native_code_ratio_;
        utils::EuclidMean<int64_t> avg_compile_time_;
        std::atomic<uint32_t> max_native_code_size_{0};
        std::atomic<uint32_t> max_compiled_bytecode_size_{0};
        std::atomic<uint64_t> num_compiled_contracts_{0};
        std::atomic<int64_t> max_compile_time_{0};
        std::atomic<uint64_t> num_unexpected_compilation_errors_{0};
        std::atomic<uint64_t> num_size_out_of_bound_compilation_errors_{0};

        // must be called non-concurrently
        void event_new_compiled_code_cached(
            SharedIntercode const &icode, SharedNativecode const &ncode,
            auto compile_start, auto compile_end) noexcept
        {
            if constexpr (utils::collect_monad_compiler_stats) {
                switch (ncode->error_code()) {
                case Nativecode::ErrorCode::Unexpected:
                    num_unexpected_compilation_errors_.fetch_add(
                        1, std::memory_order_release);
                    break;

                case Nativecode::ErrorCode::SizeOutOfBound:
                    num_size_out_of_bound_compilation_errors_.fetch_add(
                        1, std::memory_order_release);
                    break;

                case Nativecode::ErrorCode::NoError:
                    auto const native_code_size_estimate =
                        *ncode->code_size_estimate();
                    auto const bytecode_size = *icode->code_size();
                    avg_native_code_size_.update(native_code_size_estimate);
                    avg_compiled_bytecode_size_.update(bytecode_size);
                    if (bytecode_size > 0) {
                        avg_native_code_ratio_.update(
                            static_cast<double>(native_code_size_estimate) /
                            static_cast<double>(bytecode_size));
                    }
                    num_compiled_contracts_.fetch_add(
                        1, std::memory_order_release);
                    max_native_code_size_ = std::max(
                        max_native_code_size_.load(std::memory_order_acquire),
                        native_code_size_estimate);
                    max_compiled_bytecode_size_ = std::max(
                        max_compiled_bytecode_size_.load(
                            std::memory_order_acquire),
                        bytecode_size);
                    break;
                }
                auto compile_time =
                    std::chrono::duration_cast<std::chrono::microseconds>(
                        compile_end - compile_start)
                        .count();
                avg_compile_time_.update(compile_time);
                max_compile_time_ = std::max(
                    max_compile_time_.load(std::memory_order_acquire),
                    compile_time);
            }
        }

        std::string
        print_stats(uint64_t cache_size, uint64_t cache_weight) const
        {
            if constexpr (utils::collect_monad_compiler_stats) {
                return std::format(
                    ",avg_native_code_size={}B,avg_compiled_bytecode_size={}B"
                    ",avg_native_code_ratio={:.2f}"
                    ",max_native_code_size={}B,max_compiled_bytecode_size={}B"
                    ",num_compiled_contracts={}"
                    ",avg_compile_time={}µs,max_compile_time={}µs"
                    ",num_unexpected_compilation_errors={},num_size_out_of_"
                    "bound_compilation_errors={}"
                    ",varcode_cache_size={},varcode_cache_weight={}kB",
                    avg_native_code_size_.get(),
                    avg_compiled_bytecode_size_.get(),
                    avg_native_code_ratio_.get(),
                    max_native_code_size_.load(std::memory_order_acquire),
                    max_compiled_bytecode_size_.load(std::memory_order_acquire),
                    num_compiled_contracts_.load(std::memory_order_acquire),
                    avg_compile_time_.get(),
                    max_compile_time_.load(std::memory_order_acquire),
                    num_unexpected_compilation_errors_.load(
                        std::memory_order_acquire),
                    num_size_out_of_bound_compilation_errors_.load(
                        std::memory_order_acquire),
                    cache_size,
                    cache_weight);
            }
            else {
                return "";
            }
        }
    };

    class Compiler
    {
        using CompileJobMap = tbb::concurrent_hash_map<
            evmc::bytes32,
            std::tuple<
                std::function<SharedNativecode(
                    evmc::bytes32 const &, SharedIntercode const &,
                    CompilerConfig const &)>,
                uint64_t, SharedIntercode, CompilerConfig>,
            utils::Hash32Compare>;
        using CompileJobAccessor = CompileJobMap::accessor;
        using CompileJobQueue = tbb::concurrent_queue<evmc::bytes32>;

    public:
        explicit Compiler(
            bool enable_async = true, size_t compile_job_soft_limit = 1000);

        ~Compiler();

        /// Compile `Intercode` for `revision` and return compilation result.
        template <Traits traits>
        SharedNativecode
        compile(SharedIntercode const &, CompilerConfig const & = {});

        /// Find nativecode in cache, else compile and add to cache.
        template <Traits traits>
        SharedNativecode cached_compile(
            evmc::bytes32 const &code_hash, SharedIntercode const &,
            CompilerConfig const & = {});

        /// Asynchronously compile intercode with given code hash for
        /// `revision`. Returns `true` if compile job was submitted.
        /// Returns `false` if the job was already submitted or there
        /// are too many compile jobs, so unable to submit the new job.
        template <Traits traits>
        bool async_compile(
            evmc::bytes32 const &code_hash, SharedIntercode const &,
            CompilerConfig const & = {});

        /// Lookup in the cache.
        std::optional<SharedVarcode>
        find_varcode(evmc::bytes32 const &code_hash)
        {
            return varcode_cache_.get(code_hash);
        }

        SharedVarcode try_insert_varcode(
            evmc::bytes32 const &code_hash, SharedIntercode const &icode)
        {
            return varcode_cache_.try_set(code_hash, icode);
        }

        bool is_varcode_cache_warm()
        {
            return varcode_cache_.is_warm();
        }

        void set_varcode_cache_warm_kb_threshold(std::uint32_t warm_kb)
        {
            return varcode_cache_.set_warm_cache_kb(warm_kb);
        }

        std::string print_stats() const
        {
            return stats_.print_stats(
                varcode_cache_.size(), varcode_cache_.approx_weight());
        }

        // For testing: wait for compile job queue to become empty.
        void debug_wait_for_empty_queue();

    private:
        void start_compile_thread();
        void stop_compile_thread();
        void compile_loop();
        void dispense_compile_jobs();

        static constexpr asmjit::JitAllocator::CreateParams
            asmjit_create_params_{
                .options = asmjit::JitAllocatorOptions::kUseDualMapping,
            };

        asmjit::JitRuntime asmjit_rt_;
        VarcodeCache varcode_cache_;
        CompileJobMap compile_job_map_;
        CompileJobQueue compile_job_queue_;
        std::condition_variable compile_job_cv_;
        std::mutex compile_job_mutex_;
        std::unique_lock<std::mutex> compile_job_lock_;
        std::thread compiler_thread_;
        std::atomic_flag stop_flag_;
        size_t compile_job_soft_limit_;
        bool enable_async_compilation_;

        CompilerStats stats_;
    };
}
