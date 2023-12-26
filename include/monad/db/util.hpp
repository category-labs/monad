#pragma once

#include <monad/db/config.hpp>

#include <nlohmann/json.hpp>

#include <filesystem>
#include <optional>

MONAD_DB_NAMESPACE_BEGIN

uint64_t auto_detect_start_block_number(std::filesystem::path const &);
std::optional<nlohmann::json>
read_from_file(std::filesystem::path const &, uint64_t const);

MONAD_DB_NAMESPACE_END
