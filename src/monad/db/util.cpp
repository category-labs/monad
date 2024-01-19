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
        auto const child_path = entry.path();
        if (MONAD_LIKELY(child_path.extension().string() == ".json")) {
            start_block_number = std::max(
                start_block_number,
                std::stoul(child_path.stem().string()) + 1u);
        }
    }

    return start_block_number;
}

void write_to_file(
    nlohmann::json const &j, std::filesystem::path const &root_path,
    uint64_t const block_number)
{
    auto const start_time = std::chrono::steady_clock::now();

    std::string const filename = std::to_string(block_number) + ".json";
    std::filesystem::path const file_path = root_path / filename;

    MONAD_ASSERT(!std::filesystem::exists(file_path));

    std::ofstream ofile(file_path);
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
