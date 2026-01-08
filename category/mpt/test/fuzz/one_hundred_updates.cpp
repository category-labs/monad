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

#include <category/mpt/test/fuzz/one_hundred_updates.hpp>

#include "test_fixtures_fuzz.hpp"

#include <category/core/byte_string.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <map>
#include <optional>

inline constexpr auto MAX_VALUE_SIZE = 110u;

extern "C" int LLVMFuzzerTestOneInput(uint8_t const *input, size_t bytes)
{
    ::monad::test::fuzztest_input_filler filler({input, bytes});
    auto const groups = filler.get<std::array<size_t, 100>>(
        size_t(0), ::monad::test::one_hundred_updates.size() - 1);
    auto const mods =
        filler.get<std::map<size_t, std::optional<monad::byte_string>>>(
            {0, ::monad::test::one_hundred_updates.size() - 1},
            1,
            MAX_VALUE_SIZE);

    static MONAD_TRIE_FUZZTEST_FIXTURE fixture;
    fixture.reset();
    fixture.OneHundredUpdates(groups, mods);
    return 0;
}
