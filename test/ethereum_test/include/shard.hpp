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
#include <monad/test/config.hpp>

#include <gtest/gtest.h>

#include <fnmatch.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <ranges>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

MONAD_TEST_NAMESPACE_BEGIN

// A fixture's test name: its path under the root, without minus signs, which
// the test filter reads as the start of its negative patterns.
inline std::string fixture_test_name(
    std::filesystem::path const &root, std::filesystem::path const &fixture)
{
    auto name = fixture == root
                    ? fixture.filename().string()
                    : std::filesystem::relative(fixture, root).string();
    std::ranges::replace(name, '-', '_');
    return name;
}

// Whether a name matches one of gtest's ':'-separated patterns. gtest's only
// wildcards are * and ?, so a [ is matched literally.
inline bool
matches_gtest_patterns(std::string_view const patterns, std::string const &name)
{
    for (auto const pattern : std::views::split(patterns, ':')) {
        std::string glob;
        for (char const c : pattern) {
            if (c == '[') {
                glob += "[[]";
            }
            else {
                glob += c;
            }
        }
        if (!glob.empty() &&
            ::fnmatch(glob.c_str(), name.c_str(), FNM_NOESCAPE) == 0) {
            return true;
        }
    }
    return false;
}

// Whether --gtest_filter selects the test, parsed the way gtest parses it.
inline bool matches_gtest_filter(std::string const &test)
{
    std::string_view const filter = testing::FLAGS_gtest_filter;
    auto const dash = filter.find('-');
    if (dash == std::string_view::npos) {
        return matches_gtest_patterns(filter, test);
    }
    auto const positive = filter.substr(0, dash);
    return (positive.empty() || matches_gtest_patterns(positive, test)) &&
           !matches_gtest_patterns(filter.substr(dash + 1), test);
}

// Whether gtest skips the test as disabled, by the same rule gtest uses.
inline bool is_gtest_disabled(std::string const &suite, std::string const &name)
{
    constexpr std::string_view disabled = "DISABLED_*:*/DISABLED_*";
    return !testing::FLAGS_gtest_also_run_disabled_tests &&
           (matches_gtest_patterns(disabled, suite) ||
            matches_gtest_patterns(disabled, name));
}

// The fixtures of this gtest shard. File size predicts run time, so each
// fixture gtest would run goes, largest first, to the shard with the least
// work so far, counting every root registered before it. Disabled fixtures
// never run, so every shard registers them.
inline std::vector<std::filesystem::path> fixtures_for_this_shard(
    std::string const &suite, std::filesystem::path const &root,
    std::vector<std::filesystem::path> fixtures)
{
    std::ranges::sort(fixtures);
    char const *const total = std::getenv("GTEST_TOTAL_SHARDS");
    char const *const index = std::getenv("GTEST_SHARD_INDEX");
    if (total == nullptr || index == nullptr) {
        return fixtures;
    }

    std::vector<std::filesystem::path> mine;
    std::vector<std::pair<std::uintmax_t, std::filesystem::path>> sized;
    for (auto const &fixture : fixtures) {
        auto const name = fixture_test_name(root, fixture);
        if (!matches_gtest_filter(suite + '.' + name)) {
            continue;
        }
        if (is_gtest_disabled(suite, name)) {
            mine.push_back(fixture);
            continue;
        }
        sized.emplace_back(std::filesystem::file_size(fixture), fixture);
    }
    std::ranges::sort(sized, [](auto const &a, auto const &b) {
        return a.first != b.first ? a.first > b.first : a.second < b.second;
    });

    static std::vector<std::uintmax_t> work(std::stoul(total));
    std::size_t const shard = std::stoul(index);
    MONAD_ASSERT(shard < work.size());
    for (auto const &[size, fixture] : sized) {
        auto const least = std::ranges::min_element(work);
        *least += size;
        if (static_cast<std::size_t>(least - work.begin()) == shard) {
            mine.push_back(fixture);
        }
    }
    std::ranges::sort(mine);
    return mine;
}

MONAD_TEST_NAMESPACE_END
