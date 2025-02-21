#include <gtest/gtest.h>

#include "../context_switcher.h"

#define LINUX_THREAD_DB_USER_THREADS_AM_LIBTHREAD_DB 1
#include <gdb/linux-thread-db-user-threads.h>

#include <chrono>
#include <filesystem>
#include <format>
#include <latch>
#include <mutex>
#include <stdexcept>
#include <system_error>
#include <thread>

#include <dlfcn.h>
#include <unistd.h>

// The following functions would normally be defined by a debugger loading in
// libthread_db.so
extern "C"
{
extern pid_t ps_getpid(struct ps_prochandle *)
{
    std::cout << "ps_getpid called" << std::endl;
    return getpid();
}

extern ps_err_e
ps_get_thread_area(struct ps_prochandle *, lwpid_t, int idx, psaddr_t *base)
{
    std::cout << "ps_get_thread_area called" << std::endl;
#ifdef __x86_64__
    if (idx != FS) {
        abort();
    }
    unsigned long v;
    __asm__("mov %%fs:0, %0" : "=r"(v));
    *base = (psaddr_t)v;
    return PS_OK;
#elif defined(__aarch64__)
    unsigned long v;
    __asm__("mrs %0, tpidr_el0" : "=r"(v));
    *base = (psaddr_t)v;
#else
    #error "Unknown platform"
#endif
}

extern ps_err_e ps_lgetfpregs(struct ps_prochandle *, lwpid_t, prfpregset_t *)
{
    std::cout << "ps_lgetfpregs called" << std::endl;
    return PS_ERR;
}

extern ps_err_e ps_lgetregs(struct ps_prochandle *, lwpid_t, prgregset_t)
{
    std::cout << "ps_lgetregs called" << std::endl;
    return PS_ERR;
}

extern ps_err_e
ps_lsetfpregs(struct ps_prochandle *, lwpid_t, prfpregset_t const *)
{
    std::cout << "ps_lsetfpregs called" << std::endl;
    return PS_ERR;
}

extern ps_err_e ps_lsetregs(struct ps_prochandle *, lwpid_t, prgregset_t const)
{
    std::cout << "ps_lsetregs called" << std::endl;
    return PS_ERR;
}

extern ps_err_e
ps_pdread(struct ps_prochandle *, psaddr_t obj, void *addr, size_t bytes)
{
    // std::cout << "ps_pdread called with " << obj << " " << addr << " " <<
    // bytes
    //           << std::endl;
    memcpy(addr, obj, bytes);
    return PS_OK;
}

extern ps_err_e
ps_pdwrite(struct ps_prochandle *, psaddr_t, void const *, size_t)
{
    std::cout << "ps_pdwrite called" << std::endl;
    return PS_ERR;
}

extern ps_err_e ps_pglobal_lookup(
    struct ps_prochandle *, char const *object_name, char const *sym_name,
    psaddr_t *sym_addr)
{
    *sym_addr = dlsym(RTLD_DEFAULT, sym_name);
    if (*sym_addr == nullptr) {
        std::cout << "ps_pglobal_lookup called with " << object_name << " "
                  << sym_name << " failed due to " << dlerror() << std::endl;
    }
    return (*sym_addr == nullptr) ? PS_NOSYM : PS_OK;
}
}

namespace
{
    static std::filesystem::path const &thread_db_path()
    {
        static std::filesystem::path const ret = [] {
            // read link from /proc/self/exe, then search every path upwards
            // until found
            std::filesystem::path::string_type s;
            s.resize(PATH_MAX);
            auto written = readlink("/proc/self/exe", s.data(), s.size());
            if (written == -1) {
                throw std::system_error(
                    std::error_code(errno, std::system_category()));
            }
            s.resize((size_t)written);
            std::filesystem::path path(s);
            while (!std::filesystem::exists(path / "libthread_db.so.1")) {
                path = path.parent_path();
                if (path == "/") {
                    throw std::runtime_error(std::format(
                        "Could not find libthread_db.so in any directory above "
                        "{}",
                        s));
                }
            }
            return path / "libthread_db.so.1";
        }();
        return ret;
    }

    static td_init_ftype *td_init_p;
    static td_ta_map_lwp2thr_ftype *td_ta_map_lwp2thr_p;
    static td_ta_new_ftype *td_ta_new_p;
    static td_ta_delete_ftype *td_ta_delete_p;
    static td_ta_thr_iter_ftype *td_ta_thr_iter_p;
    static td_thr_get_info_ftype *td_thr_get_info_p;
    static td_symbol_list_ftype *td_symbol_list_p;

    void load_libthread_db()
    {
        if (td_init_p != nullptr) {
            return;
        }
        std::cout << "libthread_db.so found at " << thread_db_path()
                  << std::endl;
        void *so_ref = dlopen(thread_db_path().c_str(), RTLD_NOW | RTLD_LOCAL);
        if (so_ref == nullptr) {
            throw std::runtime_error(dlerror());
        }
#define LIBTHREAD_DB_FUNCTION(symbol)                                          \
    symbol##_p = (symbol##_ftype *)dlsym(so_ref, #symbol);                     \
    if (symbol##_p == nullptr)                                                 \
        throw std::runtime_error(dlerror());
        LIBTHREAD_DB_FUNCTION(td_init)
        LIBTHREAD_DB_FUNCTION(td_ta_map_lwp2thr)
        LIBTHREAD_DB_FUNCTION(td_ta_new)
        LIBTHREAD_DB_FUNCTION(td_ta_delete)
        LIBTHREAD_DB_FUNCTION(td_ta_thr_iter)
        LIBTHREAD_DB_FUNCTION(td_thr_get_info)
        LIBTHREAD_DB_FUNCTION(td_symbol_list)
#undef LIBTHREAD_DB_FUNCTION

        auto ret = td_init_p();
        if (ret != TD_OK) {
            throw std::runtime_error(
                std::format("td_init() failed with code {}", (int)ret));
        }
    }

}

TEST(context_switcher_thread_db, loads_in)
{
#if MONAD_CONTEXT_HAVE_TSAN
    // TSAN randomly interferes with our libthread_db load
    return;
#endif
    load_libthread_db();

    // Call something not intercepted by our filter to test our passthrough
    // assembler thunks
    char const **symbols = td_symbol_list_p();
    std::cout << "The symbols provided by td_symbol_list are:";
    for (char const **p = symbols; *p != nullptr; p++) {
        std::cout << "\n   " << *p;
    }
    std::cout << std::endl;

    // Call something which is intercepted by our filter to test our
    // non-passthrough wrappers
    td_thragent_t *thragent;
    auto ec = td_ta_new_p(nullptr, &thragent);
    ASSERT_EQ(ec, TD_OK);
    EXPECT_NE(thragent, nullptr);
    ec = td_ta_delete_p(thragent);
    ASSERT_EQ(ec, TD_OK);
}

TEST(context_switcher_thread_db, enumerates_context)
{
#if MONAD_CONTEXT_HAVE_TSAN
    // TSAN spins up a background thread which messes up the hardcoded numbers
    // here
    return;
#endif
    load_libthread_db();

    static struct shared_t
    {
        std::vector<std::pair<td_thrhandle_t, td_thrinfo_t>> thread_addrs;

        void clear()
        {
            thread_addrs.clear();
        }
    } shared;

    static auto enumerate_contexts = [](char const *desc) {
        std::cout << "\n   " << desc << ":" << std::endl;
        shared.clear();
        td_thragent_t *thragent;
        auto ec = td_ta_new_p(nullptr, &thragent);
        ASSERT_EQ(ec, TD_OK);
        ASSERT_NE(thragent, nullptr);

        auto cb1 = +[](td_thrhandle_t const *th, void *user) -> int {
            auto *s = (shared_t *)user;
            s->thread_addrs.emplace_back(*th, td_thrinfo_t{});
            return 0;
        };
        ec = td_ta_thr_iter_p(
            thragent,
            cb1,
            &shared,
            TD_THR_ANY_STATE,
            INT_MIN,
            nullptr,
            (unsigned)-1);
        ASSERT_EQ(ec, TD_OK);
        std::cout << "      Found a total of " << shared.thread_addrs.size()
                  << " threads:" << std::endl;

        for (auto &i : shared.thread_addrs) {
            ec = td_thr_get_info_p(&i.first, &i.second);
            EXPECT_EQ(ec, TD_OK);
            std::cout << "         Thread " << i.first.th_unique
                      << " has tid = " << i.second.ti_tid
                      << " state = " << i.second.ti_state
                      << " type = " << i.second.ti_type
                      << "\n      LWP = " << i.second.ti_lid << std::hex
                      << " pc = " << i.second.ti_pc
                      << " sp = " << i.second.ti_sp
                      << " sp_base = " << i.second.ti_stkbase
                      << " sp_size = " << i.second.ti_stksize << std::dec
                      << std::endl;
        }
        std::cout << std::endl;

        ec = td_ta_delete_p(thragent);
        ASSERT_EQ(ec, TD_OK);
    };
    enumerate_contexts("Just main thread");
    auto const before = std::move(shared.thread_addrs);
    ASSERT_EQ(before.size(), 1);
    EXPECT_EQ(before.front().second.ti_type, TD_THR_SYSTEM);

    {
        std::mutex lock;
        std::condition_variable cond;
        std::latch l(1);
        std::thread test([&] {
            std::unique_lock g(lock);
            std::cout << "Launched test thread with tid " << gettid()
                      << ", going to sleep." << std::endl;
            l.count_down();
            cond.wait(g);
        });
        l.wait();
        {
            std::unique_lock const g(lock);
            std::this_thread::sleep_for(std::chrono::milliseconds(100));
            enumerate_contexts("Main and second system threads");
            cond.notify_all();
        }
        test.join();
    }
    ASSERT_EQ(shared.thread_addrs.size(), 2);
    for (auto const &i : shared.thread_addrs) {
        EXPECT_EQ(i.second.ti_type, TD_THR_SYSTEM);
    }

    auto run_test = [&](monad_context_switcher switcher, char const *desc) {
        std::cout << "\n\n" << desc << ":\n";
        enumerate_contexts("Main system thread no userspace threads");
        ASSERT_EQ(shared.thread_addrs.size(), 1);
        EXPECT_EQ(shared.thread_addrs.front().second.ti_type, TD_THR_SYSTEM);
        EXPECT_EQ(
            shared.thread_addrs.front().second.ti_tid,
            before.front().second.ti_tid);

        {
            struct shared_t
            {
                bool done{false}, task_done{false};
                monad_context context;
            } state;

            struct monad_context_task_head task
            {
                .user_code = +[](monad_context_task task) -> monad_c_result {
                    shared_t *shared = (shared_t *)task->user_ptr;
                    monad_context context = shared->context;
                    monad_context_switcher switcher = context->switcher;
                    std::cout
                        << "         Context goes to suspend first time ..."
                        << std::endl;
                    switcher->suspend_and_call_resume(context, nullptr);
                    std::cout << "         Context resumes first time ..."
                              << std::endl;
                    // Running context should appear as running in GDB
                    enumerate_contexts(
                        "Main system thread running userspace thread");
                    std::cout
                        << "         Context goes to suspend second time ..."
                        << std::endl;
                    switcher->suspend_and_call_resume(context, nullptr);
                    std::cout << "         Context resumes second time ..."
                              << std::endl;
                    shared->task_done = true;
                    return monad_c_make_success(0);
                },
                .user_ptr = (void *)&state, .detach = +[](monad_context_task) {}
            };

            auto ctx = monad::context::make_context(switcher, &task, {});
            state.context = ctx.get();

            enumerate_contexts("Main system thread not in use context");
            ASSERT_EQ(shared.thread_addrs.size(), 1);
            EXPECT_EQ(
                shared.thread_addrs.front().second.ti_type, TD_THR_SYSTEM);
            EXPECT_EQ(
                shared.thread_addrs.front().second.ti_tid,
                before.front().second.ti_tid);

            state.done = false;
            to_result(switcher->resume_many(
                          switcher,
                          +[](void *user_ptr,
                              monad_context fake_context) -> monad_c_result {
                              shared_t *shared = (shared_t *)user_ptr;
                              if (!shared->done) {
                                  shared->done = true;
                                  // May return, may reenter this function
                                  fake_context->switcher
                                      .load(std::memory_order_acquire)
                                      ->resume(fake_context, shared->context);
                              }
                              return monad_c_make_success(0);
                          },
                          (void *)&state))
                .value();
            ASSERT_FALSE(state.task_done);
            enumerate_contexts("Main system thread suspended userspace thread");
            ASSERT_EQ(shared.thread_addrs.size(), 2);
            EXPECT_EQ(shared.thread_addrs[0].second.ti_type, TD_THR_USER);
            EXPECT_EQ(shared.thread_addrs[0].second.ti_state, TD_THR_RUN);
            // Suspended user mode threads need to set these fields, which NPTL
            // doesn't bother doing
            EXPECT_NE(shared.thread_addrs[0].second.ti_pc, 0);
            // EXPECT_NE(shared.thread_addrs[0].second.ti_sp, 0);  // fcontext
            // switcher can't set this
            EXPECT_NE(shared.thread_addrs[0].second.ti_stkbase, nullptr);
            EXPECT_NE(shared.thread_addrs[0].second.ti_stksize, 0);
            EXPECT_EQ(shared.thread_addrs[1].second.ti_type, TD_THR_SYSTEM);

            // Running contexts should appear as running
            state.done = false;
            to_result(switcher->resume_many(
                          switcher,
                          +[](void *user_ptr,
                              monad_context fake_context) -> monad_c_result {
                              shared_t *shared = (shared_t *)user_ptr;
                              if (!shared->done) {
                                  shared->done = true;
                                  // May return, may reenter this function
                                  fake_context->switcher
                                      .load(std::memory_order_acquire)
                                      ->resume(fake_context, shared->context);
                              }
                              return monad_c_make_success(0);
                          },
                          (void *)&state))
                .value();
            ASSERT_FALSE(state.task_done);
            ASSERT_EQ(shared.thread_addrs.size(), 2);
            EXPECT_EQ(shared.thread_addrs[0].second.ti_type, TD_THR_USER);
            EXPECT_EQ(shared.thread_addrs[0].second.ti_state, TD_THR_ACTIVE);
            // As this is a running user mode thread, these fields should be
            // zero
            EXPECT_EQ(shared.thread_addrs[0].second.ti_pc, 0);
            EXPECT_EQ(shared.thread_addrs[0].second.ti_sp, 0);
            EXPECT_EQ(shared.thread_addrs[0].second.ti_stkbase, nullptr);
            EXPECT_EQ(shared.thread_addrs[0].second.ti_stksize, 0);
            EXPECT_EQ(shared.thread_addrs[1].second.ti_type, TD_THR_SYSTEM);

            // Exited contexts must not appear in GDB
            state.done = false;
            to_result(switcher->resume_many(
                          switcher,
                          +[](void *user_ptr,
                              monad_context fake_context) -> monad_c_result {
                              shared_t *shared = (shared_t *)user_ptr;
                              if (!shared->done) {
                                  shared->done = true;
                                  // May return, may reenter this function
                                  fake_context->switcher
                                      .load(std::memory_order_acquire)
                                      ->resume(fake_context, shared->context);
                              }
                              return monad_c_make_success(0);
                          },
                          (void *)&state))
                .value();
            ASSERT_TRUE(state.task_done);
            enumerate_contexts("Main system thread exited userspace thread");
            ASSERT_EQ(shared.thread_addrs.size(), 1);
            EXPECT_EQ(
                shared.thread_addrs.front().second.ti_type, TD_THR_SYSTEM);
            EXPECT_EQ(
                shared.thread_addrs.front().second.ti_tid,
                before.front().second.ti_tid);
        }

        // Once deleted, should not appear in GDB
        enumerate_contexts("Main system thread destroyed context");
        ASSERT_EQ(shared.thread_addrs.size(), 1);
        EXPECT_EQ(shared.thread_addrs.front().second.ti_type, TD_THR_SYSTEM);
        EXPECT_EQ(
            shared.thread_addrs.front().second.ti_tid,
            before.front().second.ti_tid);
    };
    run_test(
        monad::context::make_context_switcher(monad_context_switcher_sjlj)
            .get(),
        "Setjmp/Longjmp context switcher");
    run_test(
        monad::context::make_context_switcher(monad_context_switcher_fcontext)
            .get(),
        "fcontext switcher");

    // Force a capacity expansion to make sure that works
    auto switcher =
        monad::context::make_context_switcher(monad_context_switcher_sjlj);
    std::vector<monad::context::context_ptr> contexts;
    contexts.reserve(128);

    struct monad_context_task_head task
    {
        .user_code = +[](monad_context_task task) -> monad_c_result {
            monad_context context = (monad_context)task->user_ptr;
            monad_context_switcher switcher = context->switcher;
            switcher->suspend_and_call_resume(context, nullptr);
            return monad_c_make_success(0);
        },
        .user_ptr = nullptr, .detach = +[](monad_context_task) {}
    };

    for (size_t n = 0; n < contexts.capacity(); n++) {
        contexts.emplace_back(
            monad::context::make_context(switcher.get(), &task, {}));
        monad_context context = contexts.back().get();
        task.user_ptr = (void *)context;
        to_result(
            switcher->resume_many(
                switcher.get(),
                +[](void *user_ptr,
                    monad_context fake_context) -> monad_c_result {
                    monad_context *contextaddr = (monad_context *)user_ptr;
                    monad_context context = *contextaddr;
                    *contextaddr = nullptr;
                    if (context != nullptr) {
                        // May return, may reenter this function
                        fake_context->switcher.load(std::memory_order_acquire)
                            ->resume(fake_context, context);
                    }
                    return monad_c_make_success(0);
                },
                (void *)&context))
            .value();
    }
    enumerate_contexts("Main system thread and 128 suspended contexts");
    ASSERT_EQ(shared.thread_addrs.size(), contexts.capacity() + 1);
    for (size_t n = 0; n < contexts.capacity(); n++) {
        EXPECT_EQ(shared.thread_addrs[n].second.ti_type, TD_THR_USER);
        EXPECT_EQ(shared.thread_addrs[n].second.ti_state, TD_THR_RUN);
        // Suspended user mode threads need to set these fields, which NPTL
        // doesn't bother doing
        EXPECT_NE(shared.thread_addrs[n].second.ti_pc, 0);
        // EXPECT_NE(shared.thread_addrs[0].second.ti_sp, 0);  // fcontext
        // switcher can't set this
        EXPECT_NE(shared.thread_addrs[n].second.ti_stkbase, nullptr);
        EXPECT_NE(shared.thread_addrs[n].second.ti_stksize, 0);
    }
    EXPECT_EQ(
        shared.thread_addrs[contexts.capacity()].second.ti_type, TD_THR_SYSTEM);
}
