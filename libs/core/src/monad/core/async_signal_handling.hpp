#pragma once

#include <monad/config.hpp>

#include <functional>
#include <memory>

#include <sys/signalfd.h>

struct ucontext;

MONAD_NAMESPACE_BEGIN

/*! \class async_signal_handling
\brief Implement async signal handling for a production process, including
command-line tools and service processes.

As anybody with deep field experience in POSIX signals will testify, they are a
mess and very easy to get wrong. This facility implements in a single place a
universal handling implementation for the non-core-dumping asynchronous signals
which are:

* `SIGALRM`
* `SIGCHLD`
* `SIGCONT`
* `SIGHUP`
* `SIGINT`
* `SIGKILL`
* `SIGSTOP`
* `SIGTERM`
* `SIGTSTP`
* `SIGTTIN`
* `SIGTTOU`
* `SIGUSR1`
* `SIGUSR2`
* `SIGPOLL`
* `SIGPROF`
* `SIGURG`
* `SIGVTALRM`

This facility does not interfere with the core-dumping asynchronous signals as
generally one wants the core dump for these:

* `SIGQUIT`
* `SIGTRAP`
* `SIGXCPU`
* `SIGXFSZ`

It does not touch and has nothing to do with synchronous signals, there are
other facilities which are likely a better fit for those (consider
`gtest_signal_stacktrace_printer.hpp`). These are:

* `SIGABRT`
* `SIGBUS`
* `SIGFPE`
* `SIGILL`
* `SIGPIPE`
* `SIGSEGV`
* `SIGSYS`

Currently we do not support having a handler called on `SIGKILL` or `SIGSTOP`,
but this may be added in the future.

You should be aware that this universal centralised facility disables all the
non-core-dumping asynchronous signals list above for the process, so any code
which uses traditional signal handlers for async signals WILL NO LONGER WORK and
will need to be refactored to use this facility instead. Synchronous signals are
left at their default enablement and are not caught by this facility -- you will
need to install traditional signal handlers to catch those.

As newly created threads inherit the signal mask from the thread which created
them, it is important to construct this as early as possible in the process.
The ideal location is straight after `main()`. This assumes that you don't
create threads before `main()`, if you do, you will need to manually call
`disable_all_async_signals_for_this_thread()`.

## Thread safety

This implementation uses proprietary Linux facilities to have a dedicated kernel
thread deal with all non-core-dumping async signals for the process. You can
therefore call async unsafe code from within your signal handler! It will be
called from the background signal handling thread, so you still need to observe
the usual thread safety precautions. However this means there are no
restrictions to APIs which can be called or operations which can be performed
from within the signal handler.

For obvious reasons, do not block for extended periods in your signal handler
as it will prevent all other signals being handled.
*/
class async_signal_handling
{
public:
    class handler
    {
        friend class async_signal_handling;
        int const signo_;
        int const priority_;
        std::move_only_function<bool(
            const struct signalfd_siginfo &, handler *)>
            f_;

        struct protected_tag_
        {
        };

    public:
        handler(
            protected_tag_, int const signo, int const priority,
            std::move_only_function<
                bool(const struct signalfd_siginfo &, handler *)>
                f)
            : signo_(signo)
            , priority_(priority)
            , f_(std::move(f))
        {
        }

        handler(handler const &) = delete;
        handler(handler &&) = delete;
        handler &operator=(handler const &) = delete;
        handler &operator=(handler &&) = delete;
        ~handler() = default;

        //! \brief THREADSAFE You must call this when the signal has been
        //! handled at its most outer point i.e. operations have been cancelled,
        //! loops broken out of. This marks that this handler is not the cause
        //! of uninterruptible hangs.
        void mark_as_handled();
    };

    class timer
    {
        friend class async_signal_handling;
        std::move_only_function<void()> f_;
        bool fired_{false};

        struct protected_tag_
        {
        };

    public:
        timer(protected_tag_, std::move_only_function<void()> f)
            : f_(std::move(f))
        {
        }

        timer(timer const &) = delete;
        timer(timer &&) = delete;
        timer &operator=(timer const &) = delete;
        timer &operator=(timer &&) = delete;
        ~timer() = default;

        //!\brief True if the timer has fired
        bool has_fired() const noexcept
        {
            return fired_;
        }
    };

    static void install_watchdog_timer_(int signo, unsigned after_ms);
    static bool invoke_handler_(const struct signalfd_siginfo &);
    static void invoke_timers_();

private:
    struct _handler_deleter
    {
        void operator()(handler *p) const
        {
            async_signal_handling::remove_handler_(p);
        }
    };

    struct _timer_deleter
    {
        void operator()(timer *p) const
        {
            async_signal_handling::remove_invoke_after_(p);
        }
    };
    friend struct _timer_deleter;

    static void remove_handler_(handler *);
    static void remove_invoke_after_(timer *);

public:
    //! \brief The type for a signal handler
    using handler_ptr = std::unique_ptr<handler, _handler_deleter>;
    //! \brief The type for a timer routine
    using timer_ptr = std::unique_ptr<timer, _timer_deleter>;

    //! \brief Install centralised signal handling for the process. This can be
    //! safely called multiple times, but it is not threadsafe.
    async_signal_handling();
    async_signal_handling(async_signal_handling const &) = delete;
    async_signal_handling(async_signal_handling &&) = delete;
    async_signal_handling &operator=(async_signal_handling const &) = delete;
    async_signal_handling &operator=(async_signal_handling &&) = delete;
    //! \brief Uninstall centralised signal handling for the process
    ~async_signal_handling();

    /*! \brief THREADSAFE Disable triggering of all non-core-dumping async
    signals for the calling thread, letting this facility handle them instead.

    As newly created threads inherit the signal mask of their creator, normally
    you do not need to call this explicitly so long as `async_signal_handling`
    is constructed before any further threads are. If however you do create
    kernel threads early, you will need to explicitly call this within each.
    */
    static void disable_all_async_signals_for_this_thread();

    //! \brief THREADSAFE Return a string description for a signal number
    static char const *signal_description(int const signo) noexcept
        __attribute__((const));

    /*! \brief THREADSAFE Add a handler to be called when the given signal
    occurs. You may use async signal unsafe code in your handler.

    Try to avoid use for alarms and timers, use `invoke_after()` instead.
    Destroy the returned object to remove the handler.
    */
    static handler_ptr add_handler(
        int signo, int priority,
        std::move_only_function<
            bool(const struct signalfd_siginfo &, handler *)>
            handler);

    /*! \brief THREADSAFE Add a routine to be called after a given duration has
    elapsed. You may use async signal unsafe code in your handler.

    Use this in preference to `alarm()` or `setitimer()` which do not
    compose with multiple users well. Destroy the returned object to cancel.
    */
    static timer_ptr
    invoke_after(std::move_only_function<void()> routine, uint64_t ns);
};

MONAD_NAMESPACE_END
