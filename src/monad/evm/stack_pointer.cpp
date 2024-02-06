#include <monad/evm/config.hpp>
#include <monad/evm/stack_pointer.hpp>

MONAD_EVM_NAMESPACE_BEGIN

StackPointer::StackPointer(uint256_t *const ptr) noexcept
    : ptr_{ptr}
{
}

uint256_t const &StackPointer::pop() noexcept
{
    return *ptr_--;
}

void StackPointer::push(uint256_t const &v) noexcept
{
    *++ptr_ = v;
}

MONAD_EVM_NAMESPACE_END
