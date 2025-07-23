#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/monad/system_call.hpp>

#include <cstring>

MONAD_NAMESPACE_BEGIN

bool is_restricted_system_call(evmc_message const &msg)
{
    if (MONAD_UNLIKELY(msg.depth != 0)) {
        return true;
    }
    if (MONAD_UNLIKELY(msg.sender != SYSTEM_TRANSACTION_SENDER)) {
        return true;
    }
    if (MONAD_UNLIKELY(msg.kind != EVMC_CALL)) {
        return true;
    }
    if (MONAD_UNLIKELY(msg.gas != 0)) {
        return true;
    }
    if (MONAD_UNLIKELY(std::bit_cast<bytes32_t>(msg.value) != bytes32_t{})) {
        return true;
    }
    if (MONAD_UNLIKELY(
            0 != std::memcmp(
                     msg.code_address.bytes,
                     msg.recipient.bytes,
                     sizeof(evmc::address)))) {
        // implied by depth == 0?
        return true;
    }
    if (MONAD_UNLIKELY(msg.code != nullptr || msg.code_size != 0)) {
        // implied by depth == 0?
        return true;
    }
    return false;
}

MONAD_NAMESPACE_END
