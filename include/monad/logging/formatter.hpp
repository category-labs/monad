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

#include <monad/state/datum.hpp>

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

namespace
{
    using account_diff_t = monad::state::diff<std::optional<monad::Account>>;
    using account_change_set_t =
        std::unordered_map<monad::address_t, account_diff_t>;

    using value_diff_t = monad::state::diff<monad::bytes32_t>;
    using key_value_map_t = std::unordered_map<monad::bytes32_t, value_diff_t>;
    using storage_change_set_t =
        std::unordered_map<monad::address_t, key_value_map_t>;

    using code_change_set_t =
        std::unordered_map<monad::bytes32_t, monad::byte_string>;
}

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
    struct copy_loggable<monad::Transaction::Type> : std::true_type
    {
    };

    template <typename T>
    struct copy_loggable<monad::state::diff<T>>
        : std::integral_constant<bool, detail::is_registered_copyable_v<T>>
    {
    };

    template <>
    struct copy_loggable<account_change_set_t> : std::true_type
    {
    };

    template <>
    struct copy_loggable<key_value_map_t> : std::true_type
    {
    };

    template <>
    struct copy_loggable<storage_change_set_t> : std::true_type
    {
    };

    template <>
    struct copy_loggable<code_change_set_t> : std::true_type
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
struct formatter<monad::Transaction::Type> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::Transaction::Type const &t, FormatContext &ctx) const
    {
        if (t == monad::Transaction::Type::eip155) {
            fmt::format_to(ctx.out(), "eip155");
        }
        else if (t == monad::Transaction::Type::eip2930) {
            fmt::format_to(ctx.out(), "eip2930");
        }
        else if (t == monad::Transaction::Type::eip1559) {
            fmt::format_to(ctx.out(), "eip1559");
        }
        else {
            fmt::format_to(ctx.out(), "Unknown Transaction Type");
        }
        return ctx.out();
    }
};

template <typename T>
struct formatter<monad::state::diff<T>> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::state::diff<T> const &diff, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");
        fmt::format_to(
            ctx.out(), "Original: {}, Updated: {}", diff.orig, diff.updated);
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};

template <>
struct fmt::formatter<account_change_set_t> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(
        account_change_set_t const &account_change_set,
        FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");
        for (auto const &[address, diff_value] : account_change_set) {
            fmt::format_to(
                ctx.out(), "\n Address: {}, Diff: {} ", address, diff_value);
        }
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};

template <>
struct fmt::formatter<key_value_map_t> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(key_value_map_t const &changed_value, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");
        for (auto const &[key, value_diff] : changed_value) {
            fmt::format_to(ctx.out(), "Key: {}, Diff: {} ", key, value_diff);
        }
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};

template <>
struct fmt::formatter<storage_change_set_t> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto format(
        storage_change_set_t const &all_accounts_changed_value,
        FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");
        for (auto const &[address, single_account_changed_value] :
             all_accounts_changed_value) {
            fmt::format_to(
                ctx.out(),
                "\n Address: {}, Value Changes: {} ",
                address,
                single_account_changed_value);
        }
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};

template <>
struct fmt::formatter<code_change_set_t> : public monad::log::basic_formatter
{
    template <typename FormatContext>
    auto
    format(code_change_set_t const &changed_value, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");
        for (auto const &[key, value] : changed_value) {
            fmt::format_to(
                ctx.out(),
                "Key: {}, Value: {}",
                key,
                fmt::join(std::as_bytes(std::span{value}), ""));
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
        fmt::format_to(ctx.out(), "{}", intx::to_string(value, 16));
        return ctx.out();
    }
};

FMTQUILL_END_NAMESPACE
