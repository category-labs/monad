#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/mpt/branches.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/path.hpp>
#include <monad/rlp/rlp.hpp>

#include <fmt/core.h>
#include <fmt/ranges.h>

#include <boost/describe/enum_to_string.hpp>
#include <boost/describe/enumerators.hpp>

// Log byte strings as a span due to below issue
//
// https://github.com/fmtlib/fmt/issues/1621
struct FmtDefaultParse
{
    template<typename ParseContext>
    constexpr auto parse(ParseContext& ctx)
    {
      return ctx.begin();
    }
};

template <>
struct fmt::formatter<monad::mpt::Nibble>: public FmtDefaultParse
{
    auto format(monad::mpt::Nibble const& nibble, format_context& ctx) const
    {
        return fmt::format_to(ctx.out(), "{:#2x}", nibble.nibble_);
    }
};

template <>
struct fmt::formatter<monad::mpt::Path>: public FmtDefaultParse
{
    auto format(monad::mpt::Path const& path, format_context& ctx) const
    {
        return fmt::format_to(ctx.out(), "{}", path.span());
    }
};

template <>
struct fmt::formatter<monad::mpt::PathView>: public FmtDefaultParse
{
    auto format(monad::mpt::PathView const& path, format_context& ctx) const
    {
        return fmt::format_to(ctx.out(), "{}", path.span());
    }
};

template<>
struct fmt::formatter<monad::rlp::Encoding>: public FmtDefaultParse
{
    template<typename FormatContext>
    auto format(monad::rlp::Encoding const& encoding, FormatContext& ctx) const
    {
        return fmt::format_to(ctx.out(), "{::x}", encoding.span());
    }
};

template <>
struct fmt::formatter<monad::mpt::BaseNode>: public FmtDefaultParse
{
    template<typename FormatContext>
    auto format(monad::mpt::BaseNode const& node, FormatContext& ctx) const
    {
        return fmt::format_to(ctx.out(), "path_to_node={} reference={}",
                node.path_to_node_view(),
                std::span(node.reference_view()));
    }
};

template<>
struct fmt::formatter<monad::mpt::LeafNode>: public FmtDefaultParse
{
    template<typename FormatContext>
    auto format(monad::mpt::LeafNode const& node, FormatContext& ctx) const
    {
        return fmt::format_to(ctx.out(), "LeafNode[{} partial_path={} value={}]",
                static_cast<monad::mpt::BaseNode const&>(node),
                node.partial_path_, node.value_);
    }
};

template<>
struct fmt::formatter<monad::mpt::BranchNode>: public FmtDefaultParse
{
    template<typename FormatContext>
    auto format(monad::mpt::BranchNode const& node, FormatContext& ctx) const
    {
        auto out = fmt::format_to(ctx.out(), "BranchNode[{} branches=[",
                static_cast<monad::mpt::BaseNode const&>(node));

        assert(node.branches_.size() == node.child_references_.size());

        auto reference = node.child_references_.cbegin();

        for (uint8_t i = 0; i < monad::mpt::Branches::NUMBER_OF_BRANCHES; ++i) {
            if (MONAD_UNLIKELY(i != 0)) {
                out = fmt::format_to(out, ", ");
            }

            if (node.branches_.branch_exists(i)) {
                assert(reference != node.child_references_.end());

                out = fmt::format_to(out, "{::x}", std::span(*reference));
                std::advance(reference, 1);
            } else {
                out = fmt::format_to(out, "NULL");
            }
        }

        return fmt::format_to(out, "]]");
    }
};

template<>
struct fmt::formatter<monad::mpt::ExtensionNode>: public FmtDefaultParse
{
    template<typename FormatContext>
    auto format(monad::mpt::ExtensionNode const& node, FormatContext& ctx) const
    {
        return fmt::format_to(ctx.out(),
                "ExtensionNode[{} partial_path={} child_reference={::x}]",
                static_cast<monad::mpt::BaseNode const&>(node),
                node.partial_path_, std::span(node.child_reference_));
    }
};

// shamelessly taken from the boost org (thanks!)
template<class T> struct fmt::formatter<T, char, std::enable_if_t<
    boost::describe::has_describe_enumerators<T>::value>>
{
private:

    using U = std::underlying_type_t<T>;

    fmt::formatter<fmt::string_view, char> sf_;
    fmt::formatter<U, char> nf_;

public:

    constexpr auto parse( format_parse_context& ctx )
    {
        auto i1 = sf_.parse( ctx );
        auto i2 = nf_.parse( ctx );

        if( i1 != i2 )
        {
            ctx.error_handler().on_error( "invalid format" );
        }

        return i1;
    }

    auto format( T const& t, format_context& ctx ) const
    {
        char const * s = boost::describe::enum_to_string( t, 0 );

        if( s )
        {
            return sf_.format( s, ctx );
        }
        else
        {
            return nf_.format( static_cast<U>( t ), ctx );
        }
    }
};
