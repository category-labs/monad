#include "test_fixtures_fuzz.hpp"

#include <monad/core/byte_string.hpp>

#include <cstddef>
#include <cstdint>
#include <map>
#include <optional>
#include <vector>

inline constexpr auto MAX_VALUE_SIZE = 110u;
inline constexpr auto GENERATED_SIZE = 100ul;

extern "C" int LLVMFuzzerTestOneInput(uint8_t const *input, size_t bytes)
{
    ::monad::test::fuzztest_input_filler filler({input, bytes});
    auto kv = filler.get<std::map<monad::byte_string, monad::byte_string>>(
        {GENERATED_SIZE, GENERATED_SIZE}, 1, MAX_VALUE_SIZE);
    if (kv.size() < GENERATED_SIZE) {
        return 0;
    }
    auto groups = filler.get<std::vector<size_t>>(
        GENERATED_SIZE, size_t(0), size_t(GENERATED_SIZE - 1));
    auto mods = filler.get<std::map<size_t, std::optional<monad::byte_string>>>(
        {0, GENERATED_SIZE - 1}, 1, MAX_VALUE_SIZE);

    static MONAD_TRIE_FUZZTEST_FIXTURE fixture;
    fixture.reset();
    fixture.GeneratedKv(kv, groups, mods);
    return 0;
}
