#pragma once

#include <monad/vm/code.hpp>
#include <monad/vm/compiler/ir/x86.hpp>
#include <monad/vm/varcode_cache.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <tbb/concurrent_hash_map.h>
#include <tbb/concurrent_queue.h>

#include <asmjit/x86.h>

#include <atomic>
#include <condition_variable>
#include <thread>

namespace monad::vm
{
    using CompilerConfig = compiler::native::CompilerConfig;

    class Compiler
    {
        using CompileJobMap = tbb::concurrent_hash_map<
            evmc::bytes32,
            std::tuple<evmc_revision, SharedIntercode, CompilerConfig>,
            utils::Hash32Compare>;
        using CompileJobAccessor = CompileJobMap::accessor;
        using CompileJobQueue = tbb::concurrent_queue<evmc::bytes32>;

    public:
        explicit Compiler(
            bool enable_async = true, size_t compile_job_soft_limit = 1000);

        ~Compiler();

        /// Compile `Intercode` for `revision` and return compilation result.
        SharedNativecode compile(
            evmc_revision revision, SharedIntercode const &,
            CompilerConfig const & = {});

        /// Find nativecode in cache, else compile and add to cache.
        SharedNativecode cached_compile(
            evmc_revision revision, evmc::bytes32 const &code_hash,
            SharedIntercode const &, CompilerConfig const & = {});

        /// Asynchronously compile intercode with given code hash for
        /// `revision`. Returns `true` if compile job was submitted.
        /// Returns `false` if the job was already submitted or there
        /// are too many compile jobs, so unable to submit the new job.
        bool async_compile(
            evmc_revision revision, evmc::bytes32 const &code_hash,
            SharedIntercode const &, CompilerConfig const & = {});

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

        // For testing: wait for compile job queue to become empty.
        void debug_wait_for_empty_queue();

    private:
        void start_compile_thread();
        void stop_compile_thread();
        void compile_loop();
        void dispense_compile_jobs();

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
    };
}
