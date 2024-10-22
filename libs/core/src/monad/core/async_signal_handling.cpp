#include "async_signal_handling.hpp"

// #define MONAD_ASYNC_SIGNAL_HANDLING_LOGGING 1

#include <monad/core/assert.h>
#include <monad/core/scope_polyfill.hpp>
#include <monad/core/tl_tid.h>

#include <chrono>
#include <csignal>
#include <cstring>
#include <iostream>
#include <latch>
#include <map>
#include <mutex>
#include <stop_token>
#include <system_error>
#include <thread>
#include <tuple>
#include <utility>

#include <poll.h>
#include <sys/ptrace.h>
#include <sys/signalfd.h>
#include <sys/ucontext.h>

MONAD_NAMESPACE_BEGIN

namespace detail
{
    static constexpr int async_signals_core_dumping[] = {
        SIGQUIT, SIGTRAP, SIGXCPU, SIGXFSZ};

    static constexpr int async_signals_non_core_dumping[] = {
        SIGALRM,
        SIGCHLD,
        SIGCONT,
        SIGHUP,
        SIGINT,
        SIGKILL,
        SIGSTOP,
        SIGTERM,
        SIGTSTP,
        SIGTTIN,
        SIGTTOU,
        SIGUSR1,
        SIGUSR2,
        SIGPOLL,
        SIGPROF,
        SIGURG,
        SIGVTALRM};

    static constexpr int sync_signals[] = {
        SIGABRT, SIGBUS, SIGFPE, SIGILL, SIGPIPE, SIGSEGV, SIGSYS};

    static void *const please_wake_up_magic =
        std::bit_cast<void *>((uintptr_t)0xd15ea5eddeadbeef);

    static struct async_signal_handling_impl_t
    {
        std::atomic<int> instance_count{0};

        struct handler_head_t
        {
            std::mutex lock;
            std::multimap<
                int, async_signal_handling::handler, std::greater<int>>
                by_priority;

            struct
            {
                async_signal_handling::timer_ptr timer;
                async_signal_handling::handler *initiated_handling;
            } watchdog;
        } handlers[64];

        struct timer_head_t
        {
            std::mutex lock;
            std::multimap<
                std::chrono::steady_clock::time_point,
                async_signal_handling::timer>
                pending, fired;
        } timers;

        static thread_local std::map<
            int, async_signal_handling::handler, std::greater<int>>::iterator
            thread_local_iterator;
        std::jthread thread;
        int thread_id;
        std::optional<std::latch> thread_ready;

        // NOTE: Runs in a different kernel thread
        void signal_handling_thread(std::stop_token done)
        {
            (void)async_signals_core_dumping;
            (void)sync_signals;
            pthread_setname_np(pthread_self(), "signal handling");
            thread_id = get_tl_tid();
            int fd;
            {
                sigset_t set;
                sigemptyset(&set);
                for (int signo : detail::async_signals_non_core_dumping) {
                    sigaddset(&set, signo);
                }
                fd = signalfd(-1, &set, SFD_NONBLOCK | SFD_CLOEXEC);
                if (fd == -1) {
                    int const errcode = errno;
                    std::cerr << "FATAL: Creating signalfd failed with '"
                              << strerror(errcode) << "'." << std::endl;
                    std::terminate();
                }
            }
            auto unfd = make_scope_exit([&]() noexcept { ::close(fd); });
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
            std::cout << "*** async signal handling thread starts on thread "
                      << get_tl_tid() << std::endl;
#endif
            async_signal_handling::disable_all_async_signals_for_this_thread();
            thread_ready->count_down();
            while (!done.stop_requested()) {
                int timeout_ms = -1;
                std::unique_lock g_timers(timers.lock);
                if (!timers.pending.empty()) {
                    auto const now = std::chrono::steady_clock::now();
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
                    std::cout
                        << "*** async signal handling thread first timer from "
                           "now = "
                        << std::chrono::duration_cast<std::chrono::nanoseconds>(
                               timers.pending.begin()->first - now)
                               .count()
                        << std::endl;
#endif
                    if (timers.pending.begin()->first <= now) {
                        timeout_ms = 0;
                    }
                    else {
                        timeout_ms = (int)std::chrono::duration_cast<
                                         std::chrono::milliseconds>(
                                         timers.pending.begin()->first - now +
                                         std::chrono::microseconds(500))
                                         .count();
                    }
                }
                g_timers.unlock();
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
                std::cout
                    << "*** async signal handling thread goes to sleep for "
                    << timeout_ms << " ms." << std::endl;
#endif
                struct pollfd fds[1] = {
                    {.fd = fd,
                     .events = POLLIN | POLLPRI | POLLERR | POLLHUP,
                     .revents = 0}};
                if (::poll(fds, 1, timeout_ms) == -1) {
                    int const errcode = errno;
                    std::cerr << "FATAL: Waiting on signalfd failed with '"
                              << strerror(errcode) << "'." << std::endl;
                    std::terminate();
                }
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
                std::cout << "*** async signal handling thread wakes revents = "
                          << fds[0].revents << "." << std::endl;
#endif
                async_signal_handling::invoke_timers_();
                struct signalfd_siginfo si = {};
                ssize_t bytesread = ::read(fd, &si, sizeof(si));
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
                std::cout << "*** async signal handling thread reads "
                          << bytesread << " bytes from signalfd." << std::endl;
#endif
                if (bytesread == -1) {
                    int const errcode = errno;
                    if (errcode != EAGAIN) {
                        std::cerr
                            << "FATAL: Reading from signalfd failed with '"
                            << strerror(errcode) << "'." << std::endl;
                        std::terminate();
                    }
                    continue;
                }
                MONAD_ASSERT(
                    si.ssi_signo < sizeof(handlers) / sizeof(handlers[0]));
                if (bytesread == 0 ||
                    (si.ssi_signo == SIGALRM &&
                     (void *)si.ssi_ptr == please_wake_up_magic)) {
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
                    std::cout << "*** async signal handling thread sees "
                                 "please_wake_up_magic, continuing"
                              << std::endl;
#endif
                    continue;
                }
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
                std::cout << "*** async signal handling thread invokes "
                             "handlers for signal "
                          << async_signal_handling::signal_description(
                                 (int)si.ssi_signo)
                          << " (" << si.ssi_signo << ")" << std::endl;
#endif
                bool const handled = async_signal_handling::invoke_handler_(si);
                if (!handled) {
                    // Simulate the default action if the signal is unhandled
                    switch (si.ssi_signo) {
                    // These exit the process gracefully
                    case SIGALRM:
                    case SIGHUP:
                    case SIGINT:
                    case SIGKILL:
                    case SIGPIPE:
                    case SIGTERM:
                    case SIGUSR1:
                    case SIGUSR2:
                    case SIGPOLL:
                    case SIGPROF:
                    case SIGVTALRM:
                        std::cerr << "FATAL: Unhandled signal "
                                  << async_signal_handling::signal_description(
                                         (int)si.ssi_signo)
                                  << " (" << si.ssi_signo
                                  << ") received, initiating graceful abnormal "
                                     "termination."
                                  << std::endl;
                        async_signal_handling::install_watchdog_timer_(
                            (int)si.ssi_signo, 0);
                        break;
                    // Otherwise we ignore
                    default:
                        std::cerr << "WARNING: Unhandled signal "
                                  << async_signal_handling::signal_description(
                                         (int)si.ssi_signo)
                                  << " (" << si.ssi_signo
                                  << ") received, ignoring as default handling "
                                     "for that signal is to ignore."
                                  << std::endl;
                        break;
                    }
                }
            }
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
            std::cout << "*** async signal handling thread exits from thread "
                      << get_tl_tid() << std::endl;
#endif
        }

        void wake_signal_handling_thread()
        {
            if (get_tl_tid() != thread_id) {
                sigval sv;
                sv.sival_ptr = please_wake_up_magic;
                pthread_sigqueue(thread.native_handle(), SIGALRM, sv);
            }
        }
    } async_signal_handling_impl;

    thread_local std::map<
        int, async_signal_handling::handler, std::greater<int>>::iterator
        async_signal_handling_impl_t::thread_local_iterator;
}

void async_signal_handling::handler::mark_as_handled()
{
    auto &impl = detail::async_signal_handling_impl;
    MONAD_ASSERT(impl.instance_count.load(std::memory_order_acquire) > 0);
    std::unique_lock<std::mutex> g;
    if (get_tl_tid() != impl.thread_id) {
        g = std::unique_lock(impl.handlers[signo_].lock);
    }
    if (impl.handlers[signo_].watchdog.initiated_handling == this) {
        impl.handlers[signo_].watchdog.timer.reset();
        impl.handlers[signo_].watchdog.initiated_handling = nullptr;
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
        std::cout << "*** async signal handler says it has "
                     "completed handling the signal. Cancelling 30 "
                     "second watchdog countdown."
                  << std::endl;
#endif
    }
}

void async_signal_handling::install_watchdog_timer_(
    int signo, unsigned after_ms)
{
    auto &impl = detail::async_signal_handling_impl;
    auto routine = [signo, after_ms]() -> void {
        if (after_ms > 0) {
            std::cerr << "FATAL: Handler for signal "
                      << async_signal_handling::signal_description(signo)
                      << " (" << signo
                      << ") which said it had initiated handling the "
                         "signal did not call mark_as_handled() "
                         "within "
                      << (after_ms / 1000) << " seconds! Invoking exit(1)."
                      << std::endl;
        }
        // TODO: Print a lot more about what all the threads
        // are doing to debug uninterruptible sleep hangs
        impl.handlers[signo].watchdog.timer = invoke_after(
            [signo]() -> void {
                std::cerr << "FATAL: Handler for signal "
                          << async_signal_handling::signal_description(signo)
                          << " (" << signo
                          << ") invoking exit(1) did not complete "
                             "within five seconds. Now invoking "
                             "_exit(1)."
                          << std::endl;
                // TODO: Print a lot more about what all
                // the threads are doing to debug
                // uninterruptible sleep hangs
                std::thread([] { _exit(1); }).detach();
                impl.handlers[signo].watchdog.timer = invoke_after(
                    [signo]() -> void {
                        std::cerr
                            << "FATAL: Handler for signal "
                            << async_signal_handling::signal_description(signo)
                            << " (" << signo
                            << ") invoking _exit(1) did not "
                               "complete within five "
                               "seconds. Now invoking "
                               "kill(SIGKILL)."
                            << std::endl;
                        // TODO: Print a lot more about what
                        // all the threads are doing to
                        // debug uninterruptible sleep hangs

                        // NOT raise(), that sends SIGKILL to this thread not
                        // the process
                        kill(getpid(), SIGKILL);
                    },
                    5000000000ULL /* 5 secs */);
            },
            5000000000ULL /* 5 secs */);
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
        std::cout << "*** async signal handler invokes std::exit(1)."
                  << std::endl;
#endif
        std::thread([] { std::exit(1); }).detach();
    };
    if (after_ms == 0) {
        routine();
    }
    else {
        impl.handlers[signo].watchdog.timer =
            invoke_after(routine, after_ms * 1000000ULL);
    }
}

bool async_signal_handling::invoke_handler_(const struct signalfd_siginfo &si)
{
    auto &impl = detail::async_signal_handling_impl;
    MONAD_ASSERT(impl.instance_count.load(std::memory_order_acquire) > 0);
    std::unique_lock<std::mutex> g(impl.handlers[si.ssi_signo].lock);
    for (impl.thread_local_iterator =
             impl.handlers[si.ssi_signo].by_priority.begin();
         impl.thread_local_iterator !=
         impl.handlers[si.ssi_signo].by_priority.end();
         ++impl.thread_local_iterator) {
        try {
            auto it = impl.thread_local_iterator;
            auto f = std::move(impl.thread_local_iterator->second.f_);
            auto unf = make_scope_exit([&]() noexcept {
                if (it == impl.thread_local_iterator) {
                    impl.thread_local_iterator->second.f_ = std::move(f);
                }
            });
            bool const has_initiated_handling =
                f(si, &impl.thread_local_iterator->second);
            if (has_initiated_handling) {
                if (it == impl.thread_local_iterator &&
                    it->second.priority_ != INT_MIN &&
                    impl.handlers[si.ssi_signo].watchdog.initiated_handling ==
                        nullptr) {
                    impl.handlers[si.ssi_signo].watchdog.initiated_handling =
                        &it->second;
                    install_watchdog_timer_((int)si.ssi_signo, 30000);
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
                    std::cout << "*** async signal handler says it has "
                                 "initiated handling the signal. Starting 30 "
                                 "second watchdog countdown."
                              << std::endl;
#endif
                }
                return true;
            }
        }
        catch (...) {
            std::cerr << "WARNING: Async signal handler for signal "
                      << async_signal_handling::signal_description(
                             (int)si.ssi_signo)
                      << " (" << si.ssi_signo
                      << ") threw an exception. Skipping." << std::endl;
        }
    }
    return false;
}

void async_signal_handling::invoke_timers_()
{
    auto &impl = detail::async_signal_handling_impl;
    if (impl.instance_count.load(std::memory_order_acquire) > 0) {
        std::unique_lock g_timers(impl.timers.lock);
        if (!impl.timers.pending.empty()) {
            auto const now = std::chrono::steady_clock::now();
            while (!impl.timers.pending.empty() &&
                   impl.timers.pending.begin()->first <= now) {
                auto const it = impl.timers.pending.begin();
                try {
                    auto f = std::move(it->second.f_);
                    f();
                }
                catch (...) {
                    std::cerr << "WARNING: Timer routine threw an exception. "
                                 "Ignoring."
                              << std::endl;
                }
                if (it == impl.timers.pending.begin()) {
                    it->second.fired_ = true;
                    auto node = impl.timers.pending.extract(it);
                    impl.timers.fired.insert(std::move(node));
                }
            }
        }
    }
}

void async_signal_handling::remove_handler_(async_signal_handling::handler *h)
{
    auto &impl = detail::async_signal_handling_impl;
    std::unique_lock<std::mutex> g;
    if (get_tl_tid() != impl.thread_id) {
        g = std::unique_lock(impl.handlers[h->signo_].lock);
    }
    auto it = impl.handlers[h->signo_].by_priority.find(h->priority_);
    MONAD_ASSERT(it != impl.handlers[h->signo_].by_priority.end());
    while (&(it->second) != h) {
        ++it;
        MONAD_ASSERT(it != impl.handlers[h->signo_].by_priority.end());
        MONAD_ASSERT(it->second.priority_ == h->priority_);
    }
    if (it == impl.thread_local_iterator) {
        --impl.thread_local_iterator;
    }
    impl.handlers[h->signo_].by_priority.erase(it);
}

void async_signal_handling::remove_invoke_after_(
    async_signal_handling::timer *h)
{
    auto &impl = detail::async_signal_handling_impl;
    std::unique_lock<std::mutex> g;
    if (get_tl_tid() != impl.thread_id) {
        g = std::unique_lock(impl.timers.lock);
    }
    auto &touse = h->has_fired() ? impl.timers.fired : impl.timers.pending;
    for (auto it = touse.begin(); it != touse.end(); ++it) {
        if (h == &it->second) {
            touse.erase(it);
            return;
        }
    }
    MONAD_ASSERT(false);
}

async_signal_handling::async_signal_handling()
{
    auto &impl = detail::async_signal_handling_impl;
    if (0 == impl.instance_count.fetch_add(1, std::memory_order_relaxed)) {
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
        std::cout << "*** async signal handling begins installation. "
                     "am_currently_under_debugger = "
                  << detail::am_currently_under_debugger << std::endl;
#endif
        MONAD_ASSERT(
            SIGRTMAX <=
            (int)(sizeof(impl.handlers) / sizeof(impl.handlers[0])));
        // For every existing signal handler currently installed, create a
        // mirror within our framework with bottommost priority
        for (int signo : detail::async_signals_non_core_dumping) {
            struct sigaction current_sa = {};
            if (0 == sigaction(signo, nullptr, &current_sa)) {
                if ((current_sa.sa_flags & SA_SIGINFO) != 0) {
                    add_handler(
                        signo,
                        INT_MIN,
                        [current_sa](
                            const struct signalfd_siginfo &si,
                            handler *self) -> bool {
                            siginfo_t si_ = {};
                            si_.si_signo = (int)si.ssi_signo;
                            si_.si_errno = si.ssi_errno;
                            si_.si_code = si.ssi_code;

                            // Need to be careful with write ordering here,
                            // siginfo_t is mostly a union
                            switch (si_.si_signo) {
                            default:
                                si_.si_pid = (pid_t)si.ssi_pid;
                                si_.si_uid = si.ssi_uid;
                                si_.si_ptr = (void *)si.ssi_ptr;
                                break;
                            case SIGALRM:
                            case SIGPROF:
                            case SIGVTALRM:
                                si_.si_timerid = (int)si.ssi_tid;
                                si_.si_overrun = (int)si.ssi_overrun;
                                si_.si_ptr = (void *)si.ssi_ptr;
                                break;
                            case SIGCHLD:
                                si_.si_pid = (pid_t)si.ssi_pid;
                                si_.si_uid = si.ssi_uid;
                                si_.si_status = si.ssi_status;
                                si_.si_utime = (clock_t)si.ssi_utime;
                                si_.si_stime = (clock_t)si.ssi_stime;
                                break;
                            case SIGILL:
                            case SIGFPE:
                            case SIGSEGV:
                            case SIGBUS:
                                si_.si_addr = (void *)si.ssi_addr;
                                si_.si_addr_lsb = (short)si.ssi_addr_lsb;
                                // si_lower U p_key
                                // si_upper U p_key
                                // si_pkey U si_lower, si_upper
                                break;
                            case SIGPOLL:
                                si_.si_band = si.ssi_band;
                                si_.si_fd = si.ssi_fd;
                                break;
                            case SIGSYS:
                                // si_.si_trapno = (int) si.ssi_trapno;
                                // si_call_addr
                                // si_syscall
                                // si_arch
                                abort();
                            }
                            // TODO FIXME: We really ought to respect more of
                            // current_sa.sa_flags, but TBH I doubt any code we
                            // use would be affected if we don't
                            current_sa.sa_sigaction(
                                (int)si.ssi_signo, &si_, nullptr);
                            if ((unsigned)current_sa.sa_flags & SA_RESETHAND) {
                                std::unique_ptr<
                                    async_signal_handling::handler,
                                    async_signal_handling::_handler_deleter>
                                    p(self);
                                (void)p; // remove
                            }
                            return true; //
                        });
                }
                else if (
                    current_sa.sa_handler != SIG_DFL &&
                    current_sa.sa_handler != SIG_IGN) {
                    add_handler(
                        signo,
                        INT_MIN,
                        [current_sa](
                            const struct signalfd_siginfo &si,
                            handler *) -> bool {
                            current_sa.sa_handler((int)si.ssi_signo);
                            return true;
                        });
                }
            }
        }
        impl.thread_ready.emplace(1);
        impl.thread = std::jthread(
            [](std::stop_token tok) { impl.signal_handling_thread(tok); });
        impl.thread_ready->wait();
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
        std::cout << "*** async signal handling ends installation."
                  << std::endl;
#endif
    }
    disable_all_async_signals_for_this_thread();
}

async_signal_handling::~async_signal_handling()
{
    auto &impl = detail::async_signal_handling_impl;
    if (1 == impl.instance_count.fetch_sub(1, std::memory_order_relaxed)) {
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
        std::cout << "*** async signal handling begins uninstallation."
                  << std::endl;
#endif
        // TODO: Should really restore all the original signal handlers first
        sigset_t set;
        sigemptyset(&set);
        for (int signo : detail::async_signals_non_core_dumping) {
            sigaddset(&set, signo);
        }
        MONAD_ASSERT(!pthread_sigmask(SIG_UNBLOCK, &set, nullptr));

        impl.thread.request_stop();
        impl.wake_signal_handling_thread();
        impl.thread.join();
        for (auto &h : impl.handlers) {
            h.by_priority.clear();
            h.watchdog.timer.reset();
        }
        impl.timers.pending.clear();
        impl.timers.fired.clear();
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
        std::cout << "*** async signal handling ends uninstallation."
                  << std::endl;
#endif
    }
}

void async_signal_handling::disable_all_async_signals_for_this_thread()
{
    sigset_t set;
    sigemptyset(&set);
    for (int signo : detail::async_signals_non_core_dumping) {
        sigaddset(&set, signo);
    }
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
    std::cout << "*** async signal handling about to block signals for thread "
              << get_tl_tid() << "." << std::endl;
#endif
    if (pthread_sigmask(SIG_BLOCK, &set, nullptr) != 0) {
        int const errcode = errno;
        std::cerr << "FATAL: pthread_sigmask has failed due to '"
                  << strerror(errcode) << "'." << std::endl;
        std::terminate();
    }
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
    std::cout
        << "*** async signal handling has finished blocking signals for thread "
        << get_tl_tid() << "." << std::endl;
#endif
}

char const *async_signal_handling::signal_description(int const signo) noexcept
{
    switch (signo) {
    default:
        return "unknown";
#define MONAD_ASYNC_SIGNAL_HANDLING_TEXT(s)                                    \
    case s:                                                                    \
        return #s
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGQUIT);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGTRAP);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGXCPU);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGXFSZ);

        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGALRM);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGCHLD);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGCONT);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGHUP);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGINT);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGKILL);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGSTOP);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGTERM);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGTSTP);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGTTIN);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGTTOU);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGUSR1);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGUSR2);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGPOLL);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGPROF);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGURG);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGVTALRM);

        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGABRT);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGBUS);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGFPE);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGILL);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGPIPE);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGSEGV);
        MONAD_ASYNC_SIGNAL_HANDLING_TEXT(SIGSYS);

#undef MONAD_ASYNC_SIGNAL_HANDLING_TEXT
    }
}

std::unique_ptr<
    async_signal_handling::handler, async_signal_handling::_handler_deleter>
async_signal_handling::add_handler(
    int signo, int priority,
    std::move_only_function<bool(const struct signalfd_siginfo &, handler *)>
        handler)
{
    auto &impl = detail::async_signal_handling_impl;
    MONAD_ASSERT(impl.instance_count.load(std::memory_order_acquire) > 0);
    std::unique_lock<std::mutex> g;
    if (get_tl_tid() != impl.thread_id) {
        g = std::unique_lock(impl.handlers[signo].lock);
    }
    auto it = impl.handlers[signo].by_priority.emplace(
        std::piecewise_construct,
        std::forward_as_tuple(priority),
        std::forward_as_tuple(
            async_signal_handling::handler::protected_tag_{},
            signo,
            priority,
            std::move(handler)));
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
    std::cout << "*** async signal handler add handler for signal "
              << async_signal_handling::signal_description(signo) << " ("
              << signo << ")" << std::endl;
#endif
    return std::unique_ptr<
        async_signal_handling::handler,
        async_signal_handling::_handler_deleter>(&it->second);
}

std::unique_ptr<
    async_signal_handling::timer, async_signal_handling::_timer_deleter>
async_signal_handling::invoke_after(
    std::move_only_function<void()> routine, uint64_t ns)
{
    auto &impl = detail::async_signal_handling_impl;
    MONAD_ASSERT(impl.instance_count.load(std::memory_order_acquire) > 0);
    auto const deadline =
        std::chrono::steady_clock::now() + std::chrono::nanoseconds(ns);
    std::unique_lock<std::mutex> g;
    if (get_tl_tid() != impl.thread_id) {
        g = std::unique_lock(impl.timers.lock);
    }
    auto it = impl.timers.pending.emplace(
        std::piecewise_construct,
        std::forward_as_tuple(deadline),
        std::forward_as_tuple(
            async_signal_handling::timer::protected_tag_{},
            std::move(routine)));
#if MONAD_ASYNC_SIGNAL_HANDLING_LOGGING
    std::cout << "*** async signal handler add invoke after " << ns
              << std::endl;
#endif
    impl.wake_signal_handling_thread();
    return std::unique_ptr<
        async_signal_handling::timer,
        async_signal_handling::_timer_deleter>(&it->second);
}

MONAD_NAMESPACE_END
