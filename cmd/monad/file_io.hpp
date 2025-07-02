#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/monad_block.hpp>

#include <filesystem>

MONAD_NAMESPACE_BEGIN

MonadConsensusBlockHeader
read_header(bytes32_t const &, std::filesystem::path const &);

MonadConsensusBlockBody
read_body(bytes32_t const &, std::filesystem::path const &);

bytes32_t head_pointer_to_id(std::filesystem::path const &);

MONAD_NAMESPACE_END
