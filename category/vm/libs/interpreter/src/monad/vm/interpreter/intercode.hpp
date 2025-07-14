#pragma once

#include <cstdint>
#include <memory>
#include <span>
#include <vector>

namespace monad::vm::interpreter
{
    class Intercode
    {
        // 30 bytes of initial padding ensures that we can implement all
        // PUSHN opcodes by reading data from _before_ the instruction
        // pointer with a single 32-byte read, then cleaning up any
        // over-read in the result value.
        static constexpr std::size_t start_padding_size = 30;

        // 32 for a truncated PUSH32, 1 for a STOP so that we don't have to
        // worry about going off the end.
        static constexpr std::size_t end_padding_size = 32 + 1;

    public:
        using JumpdestMap = std::vector<bool>;

        explicit Intercode(std::span<std::uint8_t const> const);

        Intercode(std::uint8_t const *code, std::size_t code_size)
            : Intercode{std::span<std::uint8_t const>{code, code_size}}
        {
        }

        ~Intercode();

        std::uint8_t const *code() const noexcept
        {
            return padded_code_;
        }

        std::size_t code_size() const noexcept
        {
            return code_size_;
        }

        bool is_jumpdest(std::size_t const pc) const noexcept
        {
            return pc < code_size_ && jumpdest_map_[pc];
        }

    private:
        std::uint8_t const *padded_code_;
        std::size_t code_size_;
        JumpdestMap jumpdest_map_;

        static std::uint8_t const *
        pad(std::span<std::uint8_t const> const code);

        static JumpdestMap
        find_jumpdests(std::span<std::uint8_t const> const code);
    };
}
