#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/db/config.hpp>
#include <monad/db/util.hpp>

#include <nlohmann/json.hpp>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <optional>
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

std::optional<nlohmann::json> read_from_file(
    std::filesystem::path const &root, uint64_t const start_block_number)
{
    MONAD_DEBUG_ASSERT(start_block_number != 0);

    std::string const filename =
        std::to_string(start_block_number - 1) + ".json";
    std::filesystem::path const file_path = root / filename;

    if (!std::filesystem::exists(file_path)) {
        return std::nullopt;
    }

    nlohmann::json res;

    std::ifstream ifile(file_path);
    ifile >> res;

    return std::make_optional(res);
}

MONAD_DB_NAMESPACE_END
