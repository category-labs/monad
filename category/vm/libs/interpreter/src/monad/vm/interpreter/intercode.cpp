#include <monad/vm/evm/opcodes.hpp>
#include <monad/vm/interpreter/intercode.hpp>

#include <algorithm>
#include <cstdint>
#include <span>

using namespace monad::vm::compiler;

namespace monad::vm::interpreter
{
    Intercode::Intercode(std::span<std::uint8_t const> const code)
        : padded_code_(pad(code))
        , code_size_(code.size())
        , jumpdest_map_(find_jumpdests(code))
    {
    }

    Intercode::~Intercode()
    {
        delete[] (padded_code_ - start_padding_size);
    }

    std::uint8_t const *Intercode::pad(std::span<std::uint8_t const> const code)
    {
        auto *buffer = new std::uint8_t
            [start_padding_size + code.size() + end_padding_size];

        std::fill_n(&buffer[0], start_padding_size, 0);
        std::copy(code.begin(), code.end(), &buffer[start_padding_size]);
        std::fill_n(
            &buffer[code.size() + start_padding_size], end_padding_size, 0);

        return buffer + start_padding_size;
    }

    auto Intercode::find_jumpdests(std::span<std::uint8_t const> const code)
        -> JumpdestMap
    {
        auto jumpdests = JumpdestMap(code.size(), false);

        for (auto i = 0u; i < code.size(); ++i) {
            auto const op = code[i];

            if (op == EvmOpCode::JUMPDEST) {
                jumpdests[i] = true;
            }

            if (is_push_opcode(op)) {
                i += get_push_opcode_index(op);
            }
        }

        return jumpdests;
    }
}
