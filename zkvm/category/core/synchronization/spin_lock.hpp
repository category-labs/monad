// Copyright (C) 2025-26 Category Labs, Inc.
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

// zkVM mirror of category/core/synchronization/spin_lock.hpp.
//
// The zkVM guest is single-threaded, so there is no contention: the lock is
// always free and every operation is a no-op. This deliberately avoids
// std::atomic, which on SP1's rv64im target (no 'a' extension) lowers to
// __atomic_* libcalls that the bare-metal riscv toolchain ships no libatomic
// to satisfy.

#include <category/core/config.hpp>

#include <string>

MONAD_NAMESPACE_BEGIN

class SpinLock
{
public:
    bool try_lock()
    {
        return true;
    }

    void lock() {}

    void unlock() {}

    std::string print_stats()
    {
        return {};
    }
};

MONAD_NAMESPACE_END
