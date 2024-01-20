#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/db/config.hpp>
#include <monad/db/util.hpp>

#include <nlohmann/json.hpp>
#include <quill/Quill.h>

#include <filesystem>
#include <fstream>
#include <string>

MONAD_DB_NAMESPACE_BEGIN

uint64_t auto_detect_start_block_number(std::filesystem::path const &root)
{
    namespace fs = std::filesystem;

    if (!fs::exists(root)) {
        return 0u;
    }

    uint64_t start_block_number = 0u;
    for (auto const &entry : fs::directory_iterator(root)) {
        if (fs::is_directory(entry) &&
            (fs::exists(entry.path() / "state.json") ||
             (fs::exists(entry.path() / "accounts") &&
              fs::exists(entry.path() / "code")))) {
            start_block_number = std::max(
                start_block_number,
                std::stoul(entry.path().stem().string()) + 1);
        }
    }

    return start_block_number;
}

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

MONAD_DB_NAMESPACE_END
