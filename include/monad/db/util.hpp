#pragma once

#include <monad/db/config.hpp>

#include <filesystem>

MONAD_DB_NAMESPACE_BEGIN

uint64_t auto_detect_start_block_number(std::filesystem::path const &);

MONAD_DB_NAMESPACE_END
