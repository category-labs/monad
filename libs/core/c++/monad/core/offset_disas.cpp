#include <monad/config.hpp>

#include <monad/core/offset.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

namespace disas
{
    void off48_from_int(off48_t *const result, int64_t const *const offset)
    {
        *result = off48_t{*offset};
    }

    void off48_to_int(int64_t *const result, off48_t const *const offset)
    {
        *result = int64_t{*offset};
    }
}

MONAD_NAMESPACE_END
