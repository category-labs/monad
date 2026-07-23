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

#include <category/core/config.hpp>
#include <category/core/cpu_affinity.hpp>

#include <algorithm>
#include <charconv>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <string_view>
#include <vector>

#include <pthread.h>
#include <sched.h>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

bool parse_uint16(std::string_view const s, uint16_t &out)
{
    if (s.empty()) {
        return false;
    }
    auto const *const begin = s.data();
    auto const *const end = s.data() + s.size();
    auto const [ptr, ec] = std::from_chars(begin, end, out);
    return ec == std::errc{} && ptr == end;
}

std::string_view trim(std::string_view s)
{
    while (!s.empty() && s.front() == ' ') {
        s.remove_prefix(1);
    }
    while (!s.empty() && s.back() == ' ') {
        s.remove_suffix(1);
    }
    return s;
}

std::vector<uint16_t> cpus_from_env(char const *const name)
{
    char const *const spec = std::getenv(name);
    if (spec == nullptr) {
        return {};
    }
    return monad::parse_cpu_list(spec);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

std::vector<uint16_t> parse_cpu_list(std::string_view const spec)
{
    std::vector<uint16_t> cpus;
    size_t pos = 0;
    while (pos < spec.size()) {
        size_t const comma = spec.find(',', pos);
        size_t const len =
            (comma == std::string_view::npos ? spec.size() : comma) - pos;
        std::string_view const token = trim(spec.substr(pos, len));
        pos = (comma == std::string_view::npos ? spec.size() : comma + 1);
        if (token.empty()) {
            continue;
        }
        size_t const dash = token.find('-');
        if (dash == std::string_view::npos) {
            uint16_t value;
            if (parse_uint16(token, value)) {
                cpus.push_back(value);
            }
        }
        else {
            uint16_t lo;
            uint16_t hi;
            if (parse_uint16(trim(token.substr(0, dash)), lo) &&
                parse_uint16(trim(token.substr(dash + 1)), hi) && lo <= hi) {
                for (uint16_t value = lo; value <= hi; ++value) {
                    cpus.push_back(value);
                }
            }
        }
    }
    std::sort(cpus.begin(), cpus.end());
    cpus.erase(std::unique(cpus.begin(), cpus.end()), cpus.end());
    return cpus;
}

std::vector<uint16_t> worker_cpus()
{
    return cpus_from_env("MONAD_WORKER_CPUS");
}

std::vector<uint16_t> housekeeping_cpus()
{
    return cpus_from_env("MONAD_HOUSEKEEPING_CPUS");
}

std::optional<uint16_t> housekeeping_core(HousekeepingRole const role)
{
    std::vector<uint16_t> const pool = housekeeping_cpus();
    auto const index = static_cast<size_t>(role);
    if (index >= pool.size()) {
        return std::nullopt;
    }
    return pool[index];
}

bool pin_this_thread_to_cpu(uint16_t const cpu)
{
    cpu_set_t set;
    CPU_ZERO(&set);
    CPU_SET(static_cast<int>(cpu), &set);
    return pthread_setaffinity_np(pthread_self(), sizeof(set), &set) == 0;
}

bool pin_this_thread_to_workers()
{
    std::vector<uint16_t> const cpus = worker_cpus();
    if (cpus.empty()) {
        return false;
    }
    cpu_set_t set;
    CPU_ZERO(&set);
    for (uint16_t const cpu : cpus) {
        CPU_SET(static_cast<int>(cpu), &set);
    }
    return pthread_setaffinity_np(pthread_self(), sizeof(set), &set) == 0;
}

bool pin_this_thread_to_housekeeping(HousekeepingRole const role)
{
    std::optional<uint16_t> const cpu = housekeeping_core(role);
    if (!cpu.has_value()) {
        return false;
    }
    return pin_this_thread_to_cpu(*cpu);
}

MONAD_NAMESPACE_END
