// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/fmt/int_fmt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>

#include <boost/core/demangle.hpp>

#include <nlohmann/adl_serializer.hpp>
#include <nlohmann/json.hpp>

#include <charconv>
#include <format>

MONAD_NAMESPACE_BEGIN

class State;

MONAD_NAMESPACE_END

/**
 * Parses an integer from a hex string. This is needed for the primitives
 * uint8_t, uint64_t, int64_t because we need to convert into these types from a
 * hex string and it does not seem like it is easy to override the
 * nlohmann::json implementation for these types
 * @tparam T integer type
 * @param j json blob
 * @return std::nullopt if parsing integer from hex string failed, otherwise,
 * the parsed integer
 */
template <typename T>
[[nodiscard]] T integer_from_json(nlohmann::json const &j)
    requires std::is_same_v<T, int64_t> || std::is_same_v<T, uint64_t>
{
    auto error_message = [&j](auto message_suffix) {
        return fmt::format(
            "integer_from_json<{}> was called with {}, "
            "json_type: {}, error: {}",
            boost::core::demangle(typeid(T).name()),
            j.dump(),
            j.type_name(),
            message_suffix);
    };

    if (j.is_string()) {
        auto const string = j.get<std::string>();
        T value;

        if (string.starts_with("0x")) {
            std::string_view trimmed{string};
            trimmed.remove_prefix(2);
            auto const begin = trimmed.data();
            auto const end = trimmed.data() + trimmed.size();
            auto const parse_result =
                std::from_chars(begin, end, value, 16 /* hex */);
            if (parse_result.ptr != end) {
                throw std::invalid_argument{error_message(
                    "std::from_chars did not fully consume the input")};
            }
            if (parse_result.ec == std::errc{}) {
                return value;
            }
            // I hope SSO makes this OK
            std::string error_code_message;
            if (parse_result.ec == std::errc::invalid_argument) {
                error_code_message = "invalid_argument";
            }
            else if (parse_result.ec == std::errc::result_out_of_range) {
                error_code_message = "result_out_of_range";
            }
            else {
                error_code_message = "unknown";
            }
            throw std::invalid_argument{error_message(fmt::format(
                "std::from_chars failed with {} error code",
                error_code_message))};
        }
        throw std::invalid_argument{
            error_message("non-empty hexadecimal strings are supported")};
    }
    else if (j.is_number_integer()) {
        auto const value = j.get<nlohmann::json::number_float_t>();
        if (j.is_number_unsigned()) {
            if constexpr (std::is_same_v<T, uint64_t>) {
                if (value >= 0) {
                    return static_cast<T>(value);
                }
                throw std::invalid_argument{
                    error_message("could not convert a negative double to an "
                                  "unsigned integer")};
            }
            else /* if constexpr(std::is_same_v<T, int64_t>) */ {
                if (value >= std::numeric_limits<T>::min() &&
                    value <=
                        static_cast<double>(std::numeric_limits<T>::max())) {
                    return static_cast<T>(value);
                }
                throw std::invalid_argument{error_message(
                    "unsigned double did not fit into a int64_t")};
            }
        }
        else {
            if constexpr (std::is_same_v<T, uint64_t>) {
                if (value >= std::numeric_limits<T>::min() &&
                    value <=
                        static_cast<double>(std::numeric_limits<T>::max())) {
                    return static_cast<T>(value);
                }
                throw std::invalid_argument{
                    error_message("converting a signed double to an unsigned "
                                  "integer is not supported")};
            }
            else /* if constexpr(std::is_same_v<T, int64_t>) */ {
                if (value >= std::numeric_limits<T>::min() &&
                    value <=
                        static_cast<double>(std::numeric_limits<T>::max())) {
                    return static_cast<T>(value);
                }
                throw std::invalid_argument{
                    error_message("signed double did not fit into a int64_t")};
            }
        }
    }
    throw std::invalid_argument{
        error_message("only string or integer values are allowed")};
}

namespace nlohmann
{
    template <>
    struct adl_serializer<monad::Address>
    {
        static void from_json(nlohmann::json const &json, monad::Address &o)
        {
            auto const maybe_address =
                evmc::from_hex<monad::Address>(json.get<std::string>());
            if (!maybe_address) {
                throw std::invalid_argument{fmt::format(
                    "failed to convert json object {} to hexadecimal using "
                    "evm::from_hex<monad::address_t>",
                    json.dump())};
            }
            o = maybe_address.value();
        }
    };

    template <>
    struct adl_serializer<monad::uint128_t>
    {
        static void from_json(nlohmann::json const &json, monad::uint128_t &o)
        {
            o = intx::from_string<monad::uint128_t>(json.get<std::string>());
        }
    };

    template <>
    struct adl_serializer<monad::byte_string>
    {
        static void from_json(nlohmann::json const &json, monad::byte_string &o)
        {
            auto const maybe_byte_string =
                evmc::from_hex(json.get<std::string>());
            if (!maybe_byte_string) {
                throw std::invalid_argument{fmt::format(
                    "failed to convert json object {} to hexadecimal using "
                    "evm::from_hex<monad::byte_string>",
                    json.dump())};
            }
            o = maybe_byte_string.value();
        }
    };

    template <>
    struct adl_serializer<monad::bytes32_t>
    {
        static void from_json(nlohmann::json const &json, monad::bytes32_t &o)
        {
            auto const maybe_bytes32 =
                evmc::from_hex<monad::bytes32_t>(json.get<std::string>());
            if (!maybe_bytes32) {
                throw std::invalid_argument{fmt::format(
                    "failed to convert json object {} to hexadecimal using "
                    "evm::from_hex<monad::bytes32_t>",
                    json.dump())};
            }
            o = maybe_bytes32.value();
        }
    };

    template <>
    struct adl_serializer<monad::AccessList>
    {
        static void from_json(nlohmann::json const &j, monad::AccessList &o)
        {
            for (auto const &a : j) {
                std::vector<monad::bytes32_t> storage_access_list;
                for (auto const &storage_key : a.at("storageKeys")) {
                    storage_access_list.emplace_back(
                        storage_key.get<monad::bytes32_t>());
                }
                o.emplace_back(
                    a.at("address").get<monad::Address>(),
                    std::move(storage_access_list));
            }
        }
    };

    template <>
    struct adl_serializer<monad::uint256_t>
    {
        static void from_json(nlohmann::json const &json, monad::uint256_t &o)
        {
            o = intx::from_string<monad::uint256_t>(json.get<std::string>());
        }
    };

    template <>
    struct adl_serializer<monad::TransactionError>
    {
        static void
        from_json(nlohmann::json const &j, monad::TransactionError &error)
        {
            using typename monad::TransactionError;

            auto const str = j.get<std::string>();
            if (str == "TR_InitCodeLimitExceeded") {
                error = TransactionError::InitCodeLimitExceeded;
            }
            else if (str == "TR_NonceHasMaxValue") {
                error = TransactionError::NonceExceedsMax;
            }
            else if (str == "TR_IntrinsicGas") {
                error = TransactionError::IntrinsicGasGreaterThanLimit;
            }
            else if (str == "TR_FeeCapLessThanBlocks") {
                error = TransactionError::MaxFeeLessThanBase;
            }
            else if (str == "TR_GasLimitReached") {
                error = TransactionError::GasLimitReached;
            }
            else if (str == "TR_NoFunds") {
                error = TransactionError::InsufficientBalance;
            }
            else if (str == "TR_TipGtFeeCap") {
                error = TransactionError::PriorityFeeGreaterThanMax;
            }
            else if (str == "TR_TypeNotSupported") {
                error = TransactionError::TypeNotSupported;
            }
            else if (str == "SenderNotEOA") {
                error = TransactionError::SenderNotEoa;
            }
            else {
                // unhandled exception type
                MONAD_ASSERT(false);
            }
        }
    };

    template <>
    struct adl_serializer<monad::State>
    {
        static void from_json(json const &j, monad::State &state);
    };

}
