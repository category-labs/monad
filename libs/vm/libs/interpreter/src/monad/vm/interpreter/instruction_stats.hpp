#pragma once

#include <cstdint>

namespace monad::vm::interpreter::stats
{
#ifdef MONAD_VM_INTERPRETER_STATS
    void begin(std::uint8_t const opcode);
    void end();
#else
    [[gnu::always_inline]] inline void begin(std::uint8_t const) {}

    [[gnu::always_inline]] inline void end() {}
#endif
}
