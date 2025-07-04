#include <monad/vm/code.hpp>
#include <monad/vm/compiler.hpp>
#include <monad/vm/compiler/ir/x86.hpp>
#include <monad/vm/core/assert.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <atomic>
#include <cstddef>
#include <memory>
#include <thread>

namespace monad::vm
{
    Compiler::Compiler(bool enable_async, size_t compile_job_soft_limit)
        : compile_job_lock_{compile_job_mutex_}
        , compile_job_soft_limit_{compile_job_soft_limit}
        , enable_async_compilation_{enable_async}
    {
        start_compile_thread();
    }

    Compiler::~Compiler()
    {
        stop_compile_thread();
    }

    void Compiler::start_compile_thread()
    {
        stop_flag_.clear(std::memory_order_release);
        compiler_thread_ = std::thread{[this] { compile_loop(); }};
    }

    void Compiler::stop_compile_thread()
    {
        stop_flag_.test_and_set(std::memory_order_release);
        compile_job_cv_.notify_all();
        compiler_thread_.join();
    }

    SharedNativecode Compiler::compile(
        evmc_revision rev, SharedIntercode const &icode,
        CompilerConfig const &config)
    {
        return compiler::native::compile(
            asmjit_rt_, {icode->code(), icode->code_size()}, rev, config);
    }

    SharedNativecode Compiler::cached_compile(
        evmc_revision rev, evmc::bytes32 const &code_hash,
        SharedIntercode const &icode, CompilerConfig const &config)
    {
        if (auto vcode = varcode_cache_.get(code_hash)) {
            auto const &ncode = (*vcode)->nativecode();
            if (ncode != nullptr && ncode->revision() == rev) {
                return ncode;
            }
        }
        auto ncode = compile(rev, icode, config);
        varcode_cache_.set(code_hash, icode, ncode);
        return ncode;
    }

    bool Compiler::async_compile(
        evmc_revision rev, evmc::bytes32 const &code_hash,
        SharedIntercode const &icode, CompilerConfig const &config)
    {
        if (compile_job_map_.size() >= compile_job_soft_limit_) {
            return false;
        }
        // Multiple threads can get through the above limit check, so we might
        // insert more compile jobs than `compile_job_soft_limit_`. We accept
        // multiple threads getting through at approximately the same time and
        // hence go beyond the limit. This is acceptable, because we already
        // have this many contracts in memory at approximately the same time,
        // implying that the peak memory usage of the queued compile jobs will
        // be asymptotically the same as the peak memory usage of concurrently
        // executed bytecode.
        if (!compile_job_map_.insert({code_hash, {rev, icode, config}})) {
            // The compile job was already submitted.
            return false;
        }
        // Update the queue and notify the compile loop thread.
        compile_job_queue_.push(code_hash);
        compile_job_cv_.notify_all();
        return true;
    }

    void Compiler::compile_loop()
    {
        while (!stop_flag_.test(std::memory_order_acquire)) {
            // It is possible that a new compile job has arrived or the stop
            // flag has been set, so wait for at most 1 ms. The time 1 ms seems
            // reasonable, because this is roughly the time it takes to compile
            // a typical contract.
            // Another approach is to use a lock to fix these "data races".
            // However that seems to require a lock in `async_compile`, which
            // is undesirable because it is part of the fast path.
            compile_job_cv_.wait_for(
                compile_job_lock_, std::chrono::milliseconds{1});
            dispense_compile_jobs();
        }
    }

    void Compiler::dispense_compile_jobs()
    {
        evmc::bytes32 code_hash;
        while (compile_job_queue_.try_pop(code_hash) &&
               !stop_flag_.test(std::memory_order_acquire)) {
            CompileJobAccessor acc;
            bool const find_ok = compile_job_map_.find(acc, code_hash);
            MONAD_VM_ASSERT(find_ok);
            auto const &[revision, icode, config] = acc->second;

            if (MONAD_VM_LIKELY(enable_async_compilation_)) {
                // It is possible that a new async compile request with the same
                // intercode arrives right after we erase from
                // `compile_job_map_` below. Therefore we use `cached_compile`,
                // because it first checks whether the intercode is already
                // compiled.
                (void)cached_compile(revision, code_hash, icode, config);
            }
            else {
                varcode_cache_.set(
                    code_hash,
                    icode,
                    std::make_shared<Nativecode>(
                        asmjit_rt_, revision, nullptr, 0));
            }

            bool const erase_ok = compile_job_map_.erase(acc);
            MONAD_VM_ASSERT(erase_ok);
        }
    }

    void Compiler::debug_wait_for_empty_queue()
    {
        while (!compile_job_map_.empty()) {
            std::this_thread::sleep_for(std::chrono::milliseconds{1});
        }
    }
}
