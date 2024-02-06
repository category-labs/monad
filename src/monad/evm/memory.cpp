#include <monad/core/assert.h>
#include <monad/evm/config.hpp>
#include <monad/evm/fee_schedule.hpp>
#include <monad/evm/memory.hpp>
#include <monad/evm/status.hpp>
#include <monad/evm/words.hpp>

#include <cstdint>

MONAD_EVM_NAMESPACE_BEGIN

void Memory::grow(size_t const n)
{
    // 9.1 - word size is 256 bits
    MONAD_ASSERT((n % sizeof(uint256_t)) == 0);
    MONAD_ASSERT(n > memory_.size());

    // 9.1 - memory is zero-initialized
    memory_.append(n, '\0');
}

Memory::Memory()
{
    static constexpr auto initial_size = 4 * 1024;
    static_assert((initial_size % word_size) == 0);
    memory_.reserve(initial_size);
}

void Memory::replace(
    size_t const offset, size_t const size, byte_string_view const sv)
{
    MONAD_ASSERT(size <= sv.size());
    memory_.replace(offset, size, sv);
}

byte_string_view Memory::substr(size_t const offset, size_t const size) const
{
    return byte_string_view{memory_}.substr(offset, size);
}

Status Memory::grow_if_needed(
    uint64_t &gas_left, uint256_t const &offset, uint256_t const &size)
{
    static constexpr auto max_size = byte_string{}.max_size();

    if (offset > max_size || size > max_size) {
        return Status::OutOfGas;
    }

    auto const new_size = size_t{offset} + size_t{size};
    if (new_size > memory_.size()) {
        auto const new_word_size = round_up_bytes_to_words(new_size);
        auto const curr_word_size = memory_.size() / word_size;

        // Eq 318.
        auto const new_cost =
            memory_cost * new_word_size + new_word_size * new_word_size / 512;
        auto const current_cost = memory_cost * curr_word_size +
                                  curr_word_size * curr_word_size / 512;

        auto const grow_cost = new_cost - current_cost;

        if (grow_cost > gas_left) {
            return Status::OutOfGas;
        }
        grow(new_word_size * word_size);
        gas_left -= grow_cost;
    }

    return Status::Success;
}

MONAD_EVM_NAMESPACE_END
