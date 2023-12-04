#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/state2/block_state.hpp>
#include <monad/state2/block_state_ops.hpp>
#include <monad/state2/state_deltas.hpp>

MONAD_NAMESPACE_BEGIN

byte_string &
read_code(bytes32_t const &hash, Code &code, BlockState &block_state)
{
    // code
    {
        auto const it = code.find(hash);
        if (MONAD_LIKELY(it != code.end())) {
            return it->second;
        }
    }
    auto const result = block_state.read_code(hash);
    auto const [it, _] = code.try_emplace(hash, result);
    return it->second;
}

MONAD_NAMESPACE_END
