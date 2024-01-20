#pragma once

#include <monad/db/config.hpp>

#include <nlohmann/json.hpp>

#include <filesystem>

MONAD_DB_NAMESPACE_BEGIN

void write_to_file(
    nlohmann::json const &, std::filesystem::path const &, uint64_t const);
uint64_t auto_detect_start_block_number(std::filesystem::path const &);

MONAD_DB_NAMESPACE_END
