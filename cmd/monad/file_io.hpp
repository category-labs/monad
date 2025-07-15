#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/monad/core/monad_block.hpp>

#include <filesystem>

MONAD_NAMESPACE_BEGIN

MonadConsensusBlockHeader
read_header(bytes32_t const &, std::filesystem::path const &);

MonadConsensusBlockBody
read_body(bytes32_t const &, std::filesystem::path const &);

bytes32_t head_pointer_to_id(std::filesystem::path const &);

MONAD_NAMESPACE_END
