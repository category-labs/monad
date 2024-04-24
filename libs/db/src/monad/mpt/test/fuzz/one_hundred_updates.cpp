#include "test_fixtures_fuzz.hpp"

#include "one_hundred_updates.hpp"
#include <monad/core/byte_string.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <map>
#include <optional>

inline constexpr auto MAX_VALUE_SIZE = 110u;

extern "C" int LLVMFuzzerTestOneInput(uint8_t const *input, size_t bytes)
{
    ::monad::test::fuzztest_input_filler filler({input, bytes});
    auto groups = filler.get<std::array<size_t, 100>>(
        size_t(0), ::monad::test::one_hundred_updates.size() - 1);
    auto mods = filler.get<std::map<size_t, std::optional<monad::byte_string>>>(
        {0, ::monad::test::one_hundred_updates.size() - 1}, 1, MAX_VALUE_SIZE);

    static MONAD_TRIE_FUZZTEST_FIXTURE fixture;
    fixture.reset();
    fixture.OneHundredUpdates(groups, mods);
    return 0;
}
