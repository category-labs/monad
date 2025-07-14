#pragma once

#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>

#include <category/core/byte_string.hpp>

#include <boost/intrusive/slist.hpp>

#include <optional>

MONAD_MPT_NAMESPACE_BEGIN

struct Update;
using UpdateList = boost::intrusive::slist<Update>;

struct Update
    : public boost::intrusive::slist_base_hook<
          boost::intrusive::link_mode<boost::intrusive::normal_link>>
{
    NibblesView key{};
    std::optional<byte_string_view> value{std::nullopt};
    bool incarnation{false};
    UpdateList next;
    int64_t version{0};

    constexpr bool is_deletion() const noexcept
    {
        return !value.has_value() && next.empty();
    }
};

static_assert(sizeof(Update) == 80);
static_assert(alignof(Update) == 8);

// An update can mean
// 1. underlying trie updates: when opt is empty, next is set
// 2. curr trie leaf update: when opt contains a value, next = nullptr
// 3. leaf erase: when opt is empty, next = nullptr
inline Update make_update(
    NibblesView const key, monad::byte_string_view const value,
    bool const incarnation = false, UpdateList &&next = UpdateList{},
    uint64_t const version = 0) noexcept
{
    MONAD_ASSERT(version <= std::numeric_limits<int64_t>::max());
    return Update{
        .key = key,
        .value = value,
        .incarnation = incarnation,
        .next = std::move(next),
        .version = static_cast<int64_t>(version)};
}

// When updates in the nested list but not in this key value pair itself
inline Update make_update(
    monad::byte_string_view const key, UpdateList &&next,
    uint64_t const version = 0) noexcept
{
    MONAD_ASSERT(version <= std::numeric_limits<int64_t>::max());
    return Update{
        .key = key,
        .value = std::nullopt,
        .incarnation = false,
        .next = std::move(next),
        .version = static_cast<int64_t>(version)};
}

inline Update make_erase(monad::byte_string_view const key) noexcept
{
    return Update{
        .key = key,
        .value = std::nullopt,
        .incarnation = false,
        .next = UpdateList{}};
}

MONAD_MPT_NAMESPACE_END
