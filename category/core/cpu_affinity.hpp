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

#include <category/core/config.hpp>

#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

MONAD_NAMESPACE_BEGIN

// Opt-in CPU affinity helpers used to isolate housekeeping threads (the MonadDB
// worker, io_uring, the VM compiler, the logging backend) from the execution
// worker threads (the fiber pool and the main runloop thread), so that worker
// scalability can be measured without cross-contention.
//
// Both roles are configured through environment variables and are a no-op when
// their variable is unset, so ordinary runs, tools, and tests are unaffected:
//
//   MONAD_WORKER_CPUS        cores shared by the fiber worker pool + main thread
//   MONAD_HOUSEKEEPING_CPUS  pool of cores for the housekeeping threads
//
// A value is a CPU list such as "8-15", "1,3,5", or "1-3,8-15".
//
// Worker threads share the whole MONAD_WORKER_CPUS set (they are the scaling
// variable). Housekeeping threads instead each get their OWN distinct core,
// claimed by HousekeepingRole index from the sorted MONAD_HOUSEKEEPING_CPUS
// pool, so that no two housekeeping threads land on the same core. The pool
// must therefore hold at least as many cores as there are distinct roles.

// Housekeeping roles, in the order they claim dedicated cores from the sorted
// MONAD_HOUSEKEEPING_CPUS pool. Each value is an index into that pool; e.g.
// with MONAD_HOUSEKEEPING_CPUS="1-7" the SQPOLL poller gets core 1, the db
// worker core 2, the compiler core 3 and the logging backend core 4.
enum class HousekeepingRole : unsigned
{
    Sqpoll = 0, // io_uring SQPOLL kernel poller (busy-polls its core)
    DbWorker = 1, // MonadDB async worker (also parents the io_uring workers)
    Compiler = 2, // VM async compiler
    Log = 3, // Quill logging backend
};

// Parse a CPU list ("1-7", "0,2,4", "1-3,8-15") into a sorted, de-duplicated
// list of CPU indices. Returns an empty list on empty input or parse failure.
std::vector<uint16_t> parse_cpu_list(std::string_view spec);

// CPUs configured for each role, or an empty list when the corresponding
// environment variable is unset.
std::vector<uint16_t> worker_cpus();
std::vector<uint16_t> housekeeping_cpus();

// The dedicated core assigned to a housekeeping role: the role's index into the
// sorted housekeeping pool. Returns nullopt when MONAD_HOUSEKEEPING_CPUS is
// unset or the pool has fewer cores than the role's index requires.
std::optional<uint16_t> housekeeping_core(HousekeepingRole role);

// Pin the calling thread to a single CPU. Returns true on success.
bool pin_this_thread_to_cpu(uint16_t cpu);

// Pin the calling thread to the whole worker CPU set. A no-op returning false
// when MONAD_WORKER_CPUS is unset.
bool pin_this_thread_to_workers();

// Pin the calling thread to the dedicated core for a housekeeping role. A no-op
// returning false when the role has no configured core (see housekeeping_core).
bool pin_this_thread_to_housekeeping(HousekeepingRole role);

MONAD_NAMESPACE_END
