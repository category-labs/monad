#pragma once

#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <cstdint>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

namespace monad::vm::utils::evm_as
{
    struct PlainI
    {
        constexpr explicit PlainI(compiler::EvmOpCode opcode)
            : opcode(opcode)
        {
        }

        compiler::EvmOpCode opcode;
    };

    struct PushI
    {

        constexpr explicit PushI(
            compiler::EvmOpCode opcode, runtime::uint256_t const &imm)
            : opcode(opcode)
            , imm(imm)
        {
        }

        size_t n() const
        {
            return static_cast<size_t>(opcode - compiler::EvmOpCode::PUSH0);
        }

        compiler::EvmOpCode opcode;
        runtime::uint256_t imm;
    };

    // NOTE: Below PushLabelI, JumpdestI, CommentI, InvalidI have
    // explicit rule of five implementations rather than the default
    // compiler generated ones. The reason being that there is a
    // false-positive `maybe-uninitialized` memory error in libstdc++
    // which triggers for some configurations of gcc-{14,15,16}. See my
    // comment on the PR for further details:
    // https://github.com/category-labs/monad-compiler/pull/363#issuecomment-2931405074

    struct PushLabelI
    {
        constexpr explicit PushLabelI(std::string const &label)
            : label(label)
        {
        }

        ~PushLabelI() = default;

        PushLabelI(PushLabelI const &other)

            = default;

        PushLabelI(PushLabelI &&other) noexcept
        {
            label = std::move(other.label);
        }

        PushLabelI &operator=(PushLabelI const &other)
        {
            return *this = PushLabelI(other);
        }

        PushLabelI &operator=(PushLabelI &&other) noexcept
        {
            std::swap(label, other.label);
            return *this;
        }

        std::string label;
    };

    struct JumpdestI
    {
        constexpr explicit JumpdestI(std::string const &label)
            : label(label)
        {
        }

        ~JumpdestI() = default;

        JumpdestI(JumpdestI const &other)

            = default;

        JumpdestI(JumpdestI &&other) noexcept
        {
            label = std::move(other.label);
        }

        JumpdestI &operator=(JumpdestI const &other)
        {
            return *this = JumpdestI(other);
        }

        JumpdestI &operator=(JumpdestI &&other) noexcept
        {
            std::swap(label, other.label);
            return *this;
        }

        std::string label;
    };

    struct CommentI
    {
        constexpr explicit CommentI(std::string const &msg)
            : msg(msg)
        {
        }

        ~CommentI() = default;

        CommentI(CommentI const &other)

            = default;

        CommentI(CommentI &&other) noexcept
        {
            msg = std::move(other.msg);
        }

        CommentI &operator=(CommentI const &other)
        {
            return *this = CommentI(other);
        }

        CommentI &operator=(CommentI &&other) noexcept
        {
            std::swap(msg, other.msg);
            return *this;
        }

        std::string msg;
    };

    struct InvalidI
    {
        constexpr explicit InvalidI(std::string const &name)
            : name(name)
        {
        }

        constexpr explicit InvalidI()
            : name("")
        {
        }

        ~InvalidI() = default;

        InvalidI(InvalidI const &other)

            = default;

        InvalidI(InvalidI &&other) noexcept
        {
            name = std::move(other.name);
        }

        InvalidI &operator=(InvalidI const &other)
        {
            return *this = InvalidI(other);
        }

        InvalidI &operator=(InvalidI &&other) noexcept
        {
            std::swap(name, other.name);
            return *this;
        }

        std::string name{};

        bool has_name() const
        {
            return !name.empty();
        }
    };

    template <typename T>
    concept instruction_type =
        std::is_same_v<T, PlainI> || std::is_same_v<T, PushI> ||
        std::is_same_v<T, PushLabelI> || std::is_same_v<T, JumpdestI> ||
        std::is_same_v<T, CommentI> || std::is_same_v<T, InvalidI>;

    struct Instruction
    {
        using T = std::variant<
            PlainI, PushI, JumpdestI, PushLabelI, CommentI, InvalidI>;

        static bool is_jumpdest(T ins)
        {
            return std::holds_alternative<JumpdestI>(ins);
        }

        static bool is_comment(T ins)
        {
            return std::holds_alternative<CommentI>(ins);
        }

        static bool is_plain(T ins)
        {
            return std::holds_alternative<PlainI>(ins);
        }

        static bool is_push(T ins)
        {
            return std::holds_alternative<PushI>(ins);
        }

        static bool is_push_label(T ins)
        {
            return std::holds_alternative<PushLabelI>(ins);
        }

        static bool is_invalid(T ins)
        {
            return std::holds_alternative<InvalidI>(ins);
        }

        static PushI as_push(T ins)
        {
            return std::get<PushI>(ins);
        }

        static PlainI as_plain(T ins)
        {
            return std::get<PlainI>(ins);
        }

        static PushLabelI as_push_label(T ins)
        {
            return std::get<PushLabelI>(ins);
        }

        static InvalidI as_invalid(T ins)
        {
            return std::get<InvalidI>(ins);
        }
    };

    using Instructions = std::vector<Instruction::T>;
}
