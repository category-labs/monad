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

#include <gtest/gtest.h>

#include <category/core/assert.h>
#include <category/core/backtrace.hpp>

#include <csignal>
#include <cstdarg>
#include <cstddef>
#include <map>
#include <span>

#include <unistd.h>

namespace monad::test
{
    struct SignalStackTracePrinterEnvironment final
        : public ::testing::Environment
    {
        static constexpr std::pair<int, std::string_view>
            signals_to_backtrace[] = {
                {SIGABRT, "SIGABRT"},
                {SIGBUS, "SIGBUS"},
                {SIGFPE, "SIGFPE"},
                {SIGILL, "SIGILL"},
                {SIGPIPE, "SIGPIPE"},
                {SIGSEGV, "SIGSEGV"}};

        void SetUp() override
        {
            auto &signal_handlers = this->signal_handlers();
            for (auto const &signo : signals_to_backtrace) {
                struct sigaction sa;
                struct sigaction oldsa;
                memset(&sa, 0, sizeof(sa));
                memset(&oldsa, 0, sizeof(oldsa));
                sa.sa_sigaction = &signal_handler;
                sa.sa_flags = SA_SIGINFO;
                MONAD_ASSERT(0 == ::sigaction(signo.first, &sa, &oldsa));
                signal_handlers[signo.first] = oldsa;
            }
        }

        void TearDown() override {}

        static std::map<int, struct sigaction> &signal_handlers()
        {
            static std::map<int, struct sigaction> v;
            return v;
        }

        static void
        signal_handler(int signo, ::siginfo_t *siginfo, void *context) noexcept
        {
            auto const &signal_handlers =
                SignalStackTracePrinterEnvironment::signal_handlers();

            auto const *old_signal_handler = [&] {
                using handler_t = struct sigaction const *;
                auto const it = signal_handlers.find(signo);
                if (it == signal_handlers.end()) {
                    return handler_t{nullptr};
                }
                return &it->second;
            }();

            auto write = [](char const *fmt, ...) {
                va_list args;
                va_start(args, fmt);
                char buffer[1024];
                // NOTE: sprintf may call malloc, and is not guaranteed async
                // signal safe. Chances are very good it will be async signal
                // safe for how we're using it here.
                auto const written = std::min(
                    size_t(::vsnprintf(buffer, 1024, fmt, args)), size_t(1024));
                if (-1 == ::write(2, buffer, written)) {
                    abort();
                }
                va_end(args);
            };
            {
                char const *const signame = [](int signo) {
                    for (auto const &i : signals_to_backtrace) {
                        if (signo == i.first) {
                            return i.second.data();
                        }
                    }
                    return "unknown";
                }(signo);
                write(
                    "\nSignal %s (%d) occurred due to address %p:",
                    signame,
                    signo,
                    siginfo->si_addr);
                std::byte buffer[16384];
                monad::stack_backtrace::capture(buffer)->print(2, 3, true);
            }
            write("\n");
            if (old_signal_handler != nullptr) {
                if ((old_signal_handler->sa_flags & SA_SIGINFO) != 0 &&
                    old_signal_handler->sa_sigaction != nullptr) {
                    old_signal_handler->sa_sigaction(signo, siginfo, context);
                }
                else if (old_signal_handler->sa_handler == SIG_IGN) {
                    // it is ignored
                }
                else if (old_signal_handler->sa_handler == SIG_DFL) {
                    // Default action for these is to ignore
                    if (signo == SIGCHLD || signo == SIGURG
#ifdef SIGWINCH
                        || signo == SIGWINCH
#endif
#ifdef SIGINFO
                        || signo == SIGINFO
#endif
                    )
                        return;

                    // Simulate invoke the default handler.
                    // Immediate exit without running cleanup
                    _exit(127); // compatibility code with glibc's default
                                // signal handler
                }
            }
        }
    };

    static auto const *RegisterSignalStackTracePrinterEnvironment =
        ::testing::AddGlobalTestEnvironment(
            new SignalStackTracePrinterEnvironment);
}
