#pragma once

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

// TODO: This class needs to evolve once we add support for ommers
class BlockHeaderBuffer
{
    std::optional<BlockHeader> parent_header_;
    bytes32_t parent_hash_;

public:
    BlockHeaderBuffer() = default;

    void set_parent_header(BlockHeader const &parent_header);
    std::optional<BlockHeader>
    get_parent_header(bytes32_t const &parent_hash) const noexcept;
};

MONAD_NAMESPACE_END
