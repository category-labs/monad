#pragma once

#include <monad/db/config.hpp>
#include <monad/db/util.hpp>

#include <monad/execution/config.hpp>

#include <filesystem>

MONAD_DB_NAMESPACE_BEGIN

namespace detail
{
    using namespace std::literals::string_view_literals;
    constexpr auto CURRENT_DATABASE = "CURRENT"sv;
}

[[nodiscard]] inline uint64_t
auto_detect_start_block_number(std::filesystem::path const &root)
{
    namespace fs = std::filesystem;

    if (!fs::exists(root)) {
        return 0u;
    }

    uint64_t start_block_number = 0u;
    for (auto const &entry : fs::directory_iterator(root)) {
        auto const child_path = entry.path();
        if (child_path.stem().string() != detail::CURRENT_DATABASE) {
            start_block_number = std::max(
                start_block_number,
                std::stoul(child_path.stem().string()) + 1u);
        }
    }

    return start_block_number;
}

MONAD_DB_NAMESPACE_END