#include <monad/core/byte_string.hpp>
#include <monad/core/likely.h>
#include <monad/evm/code_analysis.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/opcodes.hpp>

#include <utility>
#include <vector>

MONAD_EVM_NAMESPACE_BEGIN

CodeAnalysis analyze(byte_string_view const code)
{
    // 32 possible missing bytes (due to PUSH32) + 1 more byte for Opcode::STOP
    constexpr auto padding = 32 + 1;

    byte_string padded_code;
    padded_code.reserve(code.size() + padding);
    padded_code.append(code);
    padded_code.append(padding, '\0');

    std::vector<bool> is_jump_dest(code.size());
    constexpr auto push0 = std::to_underlying(Opcode::PUSH0);
    constexpr auto push32 = std::to_underlying(Opcode::PUSH32);
    for (size_t i = 0; i < code.size();) {
        auto const op = code.at(i);
        if (op >= push0 && op <= push32) {
            i += op - push0;
            continue;
        }
        if (MONAD_UNLIKELY(static_cast<Opcode>(op) == Opcode::JUMPDEST)) {
            is_jump_dest[i] = true;
        }
        ++i;
    }

    return CodeAnalysis{.code = padded_code, .is_jump_dest = is_jump_dest};
}

MONAD_EVM_NAMESPACE_END
