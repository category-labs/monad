#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/evm/config.hpp>

#include <cstdint>

MONAD_EVM_NAMESPACE_BEGIN

enum class Status;

class Memory
{
    // 9.1 - memory is a word addressable byte array
    byte_string memory_;

    void grow(size_t);

public:
    static constexpr auto max_size = byte_string{}.max_size();

    Memory();

    void replace(size_t offset, size_t size, byte_string_view);
    byte_string_view substr(size_t offset, size_t size) const;
    Status grow_if_needed(
        uint64_t &gas_left, uint256_t const &offset, uint256_t const &size);
};

MONAD_EVM_NAMESPACE_END
