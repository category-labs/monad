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

#include "command.hpp"
#include "err_cxx.hpp"
#include "init.hpp"
#include "stream.hpp"

#include <iterator>
#include <memory>
#include <thread>
#include <vector>

#include <pthread.h>
#include <signal.h>
#include <sysexits.h>

sig_atomic_t g_should_exit;

namespace
{

void should_exit_handler(int)
{
    g_should_exit = 1;
}

} // end of anonymous namespace

int run_commands(Topology const topology)
{
    // Some commands are "one-offs" and don't need their own thread; these are
    // handled immediately on the main thread
    for (std::unique_ptr<Command> const &command : topology.commands) {
        switch (command->type) {
        case Command::Type::Info:
            run_info_command(command.get());
            break;
        case Command::Type::SectionDump:
            run_sectiondump_command(command.get());
            break;
        default:
            break;
        }
    }

    if (signal(SIGINT, should_exit_handler) == SIG_ERR) {
        err_f(EX_OSERR, "signal(3) failed");
    }

    std::vector<std::thread> threads;
    threads.reserve(size(topology.stream_thread_map));
    for (auto const &[thread_name, streams] : topology.stream_thread_map) {
        threads.emplace_back(stream_thread_main, streams);
#if !defined(__APPLE__)
        // __APPLE__ has pthread_setname_np but with a different signature
        // (sets name of current thread only) than other systems
        pthread_setname_np(threads.back().native_handle(), thread_name.c_str());
#endif
    }

    for (std::unique_ptr<Command> const &command : topology.commands) {
        if (command->type == Command::Type::HeadStat) {
            threads.emplace_back(headstat_thread_main, command.get());
#if !defined(__APPLE__)
            pthread_setname_np(threads.back().native_handle(), "headstat_thr");
#endif
        }
    }

    for (auto &thr : threads) {
        thr.join();
    }

    return 0;
}
