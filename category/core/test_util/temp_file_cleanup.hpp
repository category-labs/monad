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

#include <category/core/assert.h>

#include <chrono>
#include <cstddef>
#include <filesystem>
#include <iostream>
#include <string>
#include <string_view>
#include <system_error>

namespace monad::test
{
    // Storage pool test files are ftruncate'd, so sparse and free -- until a
    // pool is created in one, which 0xff-fills every root offsets ring chunk,
    // a zero there reading as chunk offset 0 rather than as the invalid
    // sentinel. Each leaked file therefore costs gigabytes of real blocks.
    // They are unlinked by a scope guard, which a killed process never
    // reaches: ctest tears every running test down at once on cancel or
    // timeout.
    //
    // ctest invokes each test binary many times over in parallel, so a file a
    // live sibling is still using must never be swept. Only files older than
    // any plausible single test are removed; a live one is seconds old.
    inline void remove_stale_temp_files(
        std::filesystem::path const &dir, std::string_view const prefix,
        std::chrono::hours const older_than = std::chrono::hours(1))
    {
        // `dir` is routinely a build directory or the user's cache directory,
        // where an empty prefix or a zero age would match everything.
        MONAD_ASSERT(!prefix.empty());
        MONAD_ASSERT(older_than > std::chrono::hours(0));
        std::error_code ec;
        auto const now = std::filesystem::file_time_type::clock::now();
        std::filesystem::directory_iterator it(dir, ec);
        if (ec) {
            std::cerr << "warning: cannot sweep " << dir << " for stale "
                      << prefix << "* files: " << ec.message() << "\n";
            return;
        }
        size_t removed = 0;
        size_t failed = 0;
        for (std::filesystem::directory_iterator const end; it != end;) {
            auto const entry = *it;
            auto const name = entry.path().filename().string();
            // Regular files only, and remove rather than remove_all: this
            // sweeps what mkstemp made, and a prefix that ever matches a
            // directory must not take its subtree with it.
            if (name.starts_with(prefix) && entry.is_regular_file(ec) && !ec) {
                auto const written = entry.last_write_time(ec);
                if (!ec && now - written >= older_than) {
                    // A file already gone is reported as false with ec clear,
                    // which is what a sibling process sweeping the same
                    // directory leaves behind. Counting that as a failure
                    // would report a permissions problem that is not there.
                    if (std::filesystem::remove(entry.path(), ec)) {
                        removed++;
                    }
                    else if (ec) {
                        failed++;
                    }
                }
            }
            ec.clear();
            it.increment(ec);
            if (ec) {
                std::cerr << "warning: sweep of " << dir
                          << " stopped early: " << ec.message() << "\n";
                break;
            }
        }
        // Silence here is how the leak came back unnoticed the first time: a
        // sweep that can never remove anything looks exactly like one with
        // nothing to remove.
        if (removed != 0 || failed != 0) {
            std::cerr << "swept " << removed << " stale " << prefix
                      << "* file(s) from " << dir << ", " << failed
                      << " could not be removed\n";
        }
    }

    // Sweeps once per process, however many temp files that process creates.
    // The flag is one object per program rather than one per argument pair, so
    // a second call naming a different directory or prefix would silently
    // sweep nothing; that is asserted rather than left as a trap.
    inline void remove_stale_temp_files_once(
        std::filesystem::path const &dir, std::string_view const prefix)
    {
        static std::filesystem::path const first_dir = dir;
        static std::string const first_prefix{prefix};
        MONAD_ASSERT(
            first_dir == dir && first_prefix == prefix,
            "remove_stale_temp_files_once already swept a different directory "
            "or prefix in this process; this call would do nothing");
        [[maybe_unused]] static bool const swept = [&] {
            remove_stale_temp_files(dir, prefix);
            return true;
        }();
    }
}
