#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/db/util.hpp>

#include <nlohmann/json_fwd.hpp>

#include <quill/Quill.h> // NOLINT
#include <quill/detail/LogMacros.h>

#include <chrono>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>

MONAD_NAMESPACE_BEGIN

void write_to_file(
    nlohmann::json const &j, std::filesystem::path const &root_path,
    uint64_t const block_number)
{
    auto const start_time = std::chrono::steady_clock::now();

    auto const dir = root_path / std::to_string(block_number);
    std::filesystem::create_directory(dir);
    MONAD_ASSERT(std::filesystem::is_directory(dir));

    auto const file = dir / "state.json";
    MONAD_ASSERT(!std::filesystem::exists(file));
    std::ofstream ofile(file);
    ofile << j.dump(4);

    auto const finished_time = std::chrono::steady_clock::now();
    auto const elapsed_ms =
        std::chrono::duration_cast<std::chrono::milliseconds>(
            finished_time - start_time);
    LOG_INFO(
        "Finished dumping to json file at block = {}, time elapsed = {}",
        block_number,
        elapsed_ms);
}

MONAD_NAMESPACE_END
