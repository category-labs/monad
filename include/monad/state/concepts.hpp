#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#include <monad/state/config.hpp>

#include <concepts>
#include <optional>
#include <span>

MONAD_STATE_NAMESPACE_BEGIN

// clang-format off

template <typename T>
concept account_changes = requires(T obj) {
    { obj.account_changes } -> std::ranges::range;
    { *obj.account_changes.begin() } -> std::convertible_to<std::pair<address_t, std::optional<Account>>>;
    { obj.account_changes.empty() } -> std::same_as<bool>;
};

template <typename T>
concept storage_changes = requires(T obj) {
    { obj.storage_changes } -> std::ranges::range;
    { obj.storage_changes.begin()->first } -> std::convertible_to<address_t>;
    { obj.storage_changes.begin()->second } -> std::ranges::range;
    { *obj.storage_changes.begin()->second.begin() } -> std::convertible_to<std::pair<bytes32_t, bytes32_t>>;
    { obj.storage_changes.empty() } -> std::same_as<bool>;
};

template <typename T>
concept code_changes = requires(T obj) {
    { obj.code_changes } -> std::ranges::range;
    { *obj.code_changes.begin() } -> std::convertible_to<std::pair<bytes32_t, byte_string>>;
    { obj.code_changes.empty() } -> std::same_as<bool>;
};

template <typename T>
concept changeset = account_changes<T> && storage_changes<T> && code_changes<T>;

// clang-format on

MONAD_STATE_NAMESPACE_END
