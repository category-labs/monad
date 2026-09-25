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

#if defined(__SANITIZE_ADDRESS__)
    #define MONAD_HAVE_ASAN 1
#elif defined(__has_feature)
    #if __has_feature(address_sanitizer)
        #define MONAD_HAVE_ASAN 1
    #endif
#endif

#ifdef MONAD_HAVE_ASAN
    #include <sanitizer/asan_interface.h>

    #define MONAD_ASAN_POISON(addr, size) ASAN_POISON_MEMORY_REGION(addr, size)
    #define MONAD_ASAN_UNPOISON(addr, size)                                    \
        ASAN_UNPOISON_MEMORY_REGION(addr, size)
#else
    #define MONAD_ASAN_POISON(addr, size) ((void)(addr), (void)(size))
    #define MONAD_ASAN_UNPOISON(addr, size) ((void)(addr), (void)(size))
#endif
