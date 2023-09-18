#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/logging/config.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>

#include <monad/trie/nibbles.hpp>
#include <monad/trie/node.hpp>
#include <monad/trie/update.hpp>

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>
#include <quill/bundled/fmt/ranges.h>

#include <optional>
#include <type_traits>
#include <unordered_map>

namespace fmt = fmtquill::v10;

MONAD_LOG_NAMESPACE_BEGIN
struct basic_formatter
{
    template <typename ParseContext>
    constexpr auto parse(ParseContext &ctx)
    {
        return ctx.begin();
    }
};

MONAD_LOG_NAMESPACE_END

namespace quill
{
    template <>
    struct copy_loggable<monad::Account> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::address_t> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::BlockHeader> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::bytes32_t> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::Receipt> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::Receipt::Log> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::TransactionType> : std::true_type
    {
    };

    // for both AccountDelta & StorageDelta
    template <typename T>
    struct copy_loggable<monad::delta_t<T>>
        : std::integral_constant<bool, detail::is_registered_copyable_v<T>>
    {
    };

    template <>
    struct copy_loggable<monad::StateDelta> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::StateDeltas> : std::true_type
    {
    };

    // Code
    template <>
    struct copy_loggable<monad::Code> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::trie::Nibbles> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::trie::Update> : std::true_type
    {
    };

    template <>
    struct copy_loggable<uint64_t> : std::true_type
    {
    };

    template <unsigned N>
    struct copy_loggable<intx::uint<N>> : std::true_type
    {
    };

    template <typename T>
    struct copy_loggable<std::optional<T>>
        : std::integral_constant<bool, detail::is_registered_copyable_v<T>>
    {
    };

}

FMTQUILL_BEGIN_NAMESPACE

template <>
struct formatter<monad::Account> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::Account const &a, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "Account{{"
            "balance={}, "
            "code_hash={}, "
            "nonce={}"
            "}}",
            a.balance,
            a.code_hash,
            a.nonce);
        return ctx.out();
    }
};

template <>
struct formatter<monad::address_t> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::address_t const &value, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(value.bytes)), ""));
        return ctx.out();
    }
};

template <>
struct formatter<monad::bytes32_t> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::bytes32_t const &value, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(value.bytes)), ""));
        return ctx.out();
    }
};

template <>
struct formatter<monad::BlockHeader> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::BlockHeader const &bh, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "BlockHeader{{"
            "Parent Hash={} "
            "Ommers Hash={} "
            "Beneficiary Address={} "
            "State Root={} "
            "Transaction Root={} "
            "Receipt Root={} "
            "Logs Bloom=0x{:02x} "
            "Difficulty={} "
            "Block Number={} "
            "Gas Limit={} "
            "Gas Used={} "
            "Timestamp={} "
            "Extra Data=0x{:02x}"
            "}}",
            bh.parent_hash,
            bh.ommers_hash,
            bh.beneficiary,
            bh.state_root,
            bh.transactions_root,
            bh.receipts_root,
            fmt::join(std::as_bytes(std::span(bh.logs_bloom)), ""),
            bh.difficulty,
            bh.number,
            bh.gas_limit,
            bh.gas_used,
            bh.timestamp,
            fmt::join(std::as_bytes(std::span(bh.extra_data)), ""));
        return ctx.out();
    }
};

template <>
struct formatter<monad::Receipt> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::Receipt const &r, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "Receipt{{"
            "Bloom=0x{:02x} "
            "Status={} "
            "Gas Used={} "
            "Transaction Type={} "
            "Logs={}"
            "}}",
            fmt::join(std::as_bytes(std::span(r.bloom)), ""),
            r.status,
            r.gas_used,
            r.type,
            r.logs);
        return ctx.out();
    }
};

template <>
struct formatter<monad::Receipt::Log> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::Receipt::Log const &l, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "Log{{"
            "Data=0x{:02x} "
            "Topics={} "
            "Address={}"
            "}}",
            fmt::join(std::as_bytes(std::span(l.data)), ""),
            l.topics,
            l.address);
        return ctx.out();
    }
};

template <>
struct formatter<monad::TransactionType> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::TransactionType const &t, FormatContext &ctx) const
    {
        if (t == monad::TransactionType::eip155) {
            fmt::format_to(ctx.out(), "eip155");
        }
        else if (t == monad::TransactionType::eip2930) {
            fmt::format_to(ctx.out(), "eip2930");
        }
        else if (t == monad::TransactionType::eip1559) {
            fmt::format_to(ctx.out(), "eip1559");
        }
        else {
            fmt::format_to(ctx.out(), "Unknown Transaction Type");
        }
        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::StateDelta> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::StateDelta const &state_delta, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");
        fmt::format_to(ctx.out(), "Account Delta: {} ", state_delta.account);
        fmt::format_to(ctx.out(), "Storage Deltas: {{");
        for (auto const &[key, storage_delta] : state_delta.storage) {
            fmt::format_to(
                ctx.out(), " Key: {}, Storage Delta: {}", key, storage_delta);
        }
        fmt::format_to(ctx.out(), "}}");
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::StateDeltas> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto
    format(monad::StateDeltas const &state_deltas, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");

        for (auto const &[address, state_delta] : state_deltas) {
            fmt::format_to(
                ctx.out(),
                " Address: {}, State Delta: {}",
                address,
                state_delta);
        }
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::Code> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::Code const &code, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");

        for (auto const &[code_hash, code_value] : code) {
            fmt::format_to(
                ctx.out(),
                "Code Hash: {}, Code Value: 0x{:02x} ",
                code_hash,
                fmt::join(std::as_bytes(std::span{code_value}), ""));
        }
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};

template <>
struct formatter<monad::trie::Nibbles> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::trie::Nibbles const &n, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "0x");
        for (uint8_t i = 0; i < n.size(); ++i) {
            MONAD_DEBUG_ASSERT(n[i] <= 0xf);
            fmt::format_to(ctx.out(), "{:01x}", n[i]);
        }
        return ctx.out();
    }
};

template <>
struct formatter<monad::trie::Upsert> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::trie::Upsert const &u, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "UPSERT{{key={} value=0x{:02x}}}",
            u.key,
            fmt::join(std::as_bytes(std::span{u.value}), ""));
        return ctx.out();
    }
};

template <>
struct formatter<monad::trie::Delete> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::trie::Delete const &d, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "DELETE{{key={}}}", d.key);
        return ctx.out();
    }
};

template <>
struct formatter<monad::trie::Update> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::trie::Update const &update, FormatContext &ctx) const
    {
        std::visit(
            [&ctx](auto const &u) { fmt::format_to(ctx.out(), "{}", u); },
            update);
        return ctx.out();
    }
};

template <>
struct formatter<monad::trie::Branch> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::trie::Branch const &branch, FormatContext &ctx) const
    {
        auto const format = [&](size_t i) {
            return fmt::format(
                "0x{:02x}",
                fmt::join(std::as_bytes(std::span(branch.children[i])), ""));
        };
        std::array const strings = {
            format(0),
            format(1),
            format(2),
            format(3),
            format(4),
            format(5),
            format(6),
            format(7),
            format(8),
            format(9),
            format(10),
            format(11),
            format(12),
            format(13),
            format(14),
            format(15),
        };
        static_assert(
            strings.size() == std::tuple_size<decltype(branch.children)>());

        fmt::format_to(
            ctx.out(),
            "Branch{{key_size={:d} path_to_node={} reference=0x{:02x} "
            "branches={::}}}",
            branch.key_size,
            branch.path_to_node,
            fmt::join(std::as_bytes(std::span(branch.reference)), ""),
            strings);

        return ctx.out();
    }
};

template <>
struct formatter<monad::trie::Leaf> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::trie::Leaf const &leaf, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "Leaf{{key_size={:d} path_to_node={} reference=0x{:02x} "
            "value=0x{:02x}}}",
            leaf.key_size,
            leaf.path_to_node,
            fmt::join(std::as_bytes(std::span(leaf.reference)), ""),
            fmt::join(std::as_bytes(std::span(leaf.value)), ""));
        return ctx.out();
    }
};

template <>
struct formatter<monad::trie::Node> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::trie::Node const &update, FormatContext &ctx) const
    {
        std::visit(
            [&ctx](auto const &u) { fmt::format_to(ctx.out(), "{}", u); },
            update);
        return ctx.out();
    }
};

template <unsigned N>
struct formatter<intx::uint<N>> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(intx::uint<N> const &value, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{}", intx::to_string(value, 10));
        return ctx.out();
    }
};

FMTQUILL_END_NAMESPACE
