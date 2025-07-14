#include <cstddef>

namespace monad::vm::compiler::poly_typed
{
    constexpr size_t max_kind_depth = 50;

    constexpr size_t max_kind_ticks = 10000;

    struct InferException
    {
    };

    struct DepthException : public InferException
    {
    };

    struct TickException : public InferException
    {
    };

    struct UnificationException : public InferException
    {
    };

    inline void increment_kind_depth(size_t &depth, size_t x)
    {
        depth += x;
        if (depth > max_kind_depth) {
            throw DepthException{};
        }
    }

    inline void increment_kind_ticks(size_t &ticks, size_t x)
    {
        ticks += x;
        if (ticks > max_kind_ticks) {
            throw TickException{};
        }
    }
}
