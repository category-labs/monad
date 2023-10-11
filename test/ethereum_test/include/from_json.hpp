#pragma once

#include <general_state_test_types.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/logging/formatter.hpp>

#include <boost/core/demangle.hpp>

#include <nlohmann/adl_serializer.hpp>
#include <nlohmann/json.hpp>

#include <charconv>
#include <format>

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
    struct adl_serializer<monad::address_t>
    {
        static void from_json(nlohmann::json const &json, monad::address_t &o)
        {
            auto const maybe_address =
                evmc::from_hex<monad::address_t>(json.get<std::string>());
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
    struct adl_serializer<monad::Transaction::AccessList>
    {
        static void
        from_json(nlohmann::json const &j, monad::Transaction::AccessList &o)
        {
            for (auto const &a : j) {
                std::vector<monad::bytes32_t> storage_access_list;
                for (auto const &storage_key : a.at("storageKeys")) {
                    storage_access_list.emplace_back(
                        storage_key.get<monad::bytes32_t>());
                }
                o.emplace_back(
                    a.at("address").get<monad::address_t>(),
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
    struct adl_serializer<monad::test::SharedTransactionData>
    {
        static void from_json(
            nlohmann::json const &j, monad::test::SharedTransactionData &o)
        {
            // we cannot use the nlohmann::json from_json<uint64_t> because it
            // does not use the strtoull implementation, whereas we need it so
            // we can turn a hex string into a uint64_t
            o.nonce = integer_from_json<uint64_t>(j.at("nonce"));
            o.sender = j.at("sender").get<monad::address_t>();

            if (auto const to_it = j.find("to");
                to_it != j.end() && !to_it->get<std::string>().empty()) {
                o.to = to_it->get<monad::address_t>();
            }

            if (auto const gas_price_it = j.find("gasPrice");
                gas_price_it != j.end()) {
                o.transaction_type = monad::TransactionType::eip155;
                o.max_fee_per_gas = integer_from_json<uint64_t>(*gas_price_it);
                if (j.contains("maxFeePerGas") ||
                    j.contains("maxPriorityFeePerGas")) {
                    throw std::invalid_argument(
                        "invalid transaction: contains "
                        "both legacy and EIP-1559 fees");
                }
            }
            else {
                o.transaction_type = monad::TransactionType::eip1559;
                o.max_fee_per_gas =
                    integer_from_json<uint64_t>(j.at("maxFeePerGas"));
                o.max_priority_fee_per_gas =
                    integer_from_json<uint64_t>(j.at("maxPriorityFeePerGas"));
            }

            for (auto const &j_data : j.at("data")) {
                o.inputs.emplace_back(j_data.get<monad::byte_string>());
            }

            if (auto const ac_it = j.find("accessLists"); ac_it != j.end()) {
                for (auto const &j_access_list : *ac_it)
                    o.access_lists.emplace_back(
                        j_access_list.get<monad::Transaction::AccessList>());
                if (o.transaction_type == monad::TransactionType::eip155) {
                    // Upgrade tx type if tx has
                    // access lists
                    o.transaction_type = monad::TransactionType::eip2930;
                }
            }
            if (!o.access_lists.empty()) {
                MONAD_ASSERT(o.inputs.size() == o.access_lists.size());
            }

            for (auto const &j_gas_limit : j.at("gasLimit")) {
                o.gas_limits.emplace_back(
                    integer_from_json<int64_t>(j_gas_limit));
            }

            for (auto const &j_value : j.at("value")) {
                o.values.emplace_back(j_value.get<monad::uint256_t>());
            }
        }
    };

    template <>
    struct adl_serializer<monad::test::Indices>
    {
        static void from_json(json const &j, monad::test::Indices &indices)
        {
            indices.input =
                integer_from_json<uint64_t>(j.at("data").get<uint64_t>());
            indices.gas_limit =
                integer_from_json<uint64_t>(j.at("gas").get<uint64_t>());
            indices.value =
                integer_from_json<uint64_t>(j.at("value").get<uint64_t>());
        }
    };

    template <>
    struct adl_serializer<monad::execution::TransactionStatus>
    {
        static void from_json(
            nlohmann::json const &j,
            monad::execution::TransactionStatus &status)
        {
            using namespace monad::execution;
            auto const str = j.get<std::string>();
            if (str == "TR_InitCodeLimitExceeded") {
                status = TransactionStatus::INIT_CODE_LIMIT_EXCEEDED;
            }
            else if (str == "TR_NonceHasMaxValue") {
                status = TransactionStatus::NONCE_EXCEEDS_MAX;
            }
            else if (str == "TR_IntrinsicGas") {
                status = TransactionStatus::INTRINSIC_GAS_GREATER_THAN_LIMIT;
            }
            else if (str == "TR_FeeCapLessThanBlocks") {
                status = TransactionStatus::MAX_FEE_LESS_THAN_BASE;
            }
            else if (str == "TR_GasLimitReached") {
                status = TransactionStatus::GAS_LIMIT_REACHED;
            }
            else if (str == "TR_NoFunds") {
                status = TransactionStatus::INSUFFICIENT_BALANCE;
            }
            else if (str == "TR_TipGtFeeCap") {
                status = TransactionStatus::PRIORITY_FEE_GREATER_THAN_MAX;
            }
            else if (str == "TR_TypeNotSupported") {
                status = TransactionStatus::TYPE_NOT_SUPPORTED;
            }
            else if (str == "SenderNotEOA") {
                status = TransactionStatus::SENDER_NOT_EOA;
            }
            else {
                // unhandled exception type
                MONAD_ASSERT(false);
            }
        }
    };

    template <>
    struct adl_serializer<monad::test::Expectation>
    {
        static void
        from_json(nlohmann::json const &j, monad::test::Expectation &o)
        {
            o.indices = j.at("indexes").get<monad::test::Indices>();
            o.state_hash = j.at("hash").get<monad::bytes32_t>();
            o.exception = j.contains("expectException")
                              ? j.at("expectException")
                                    .get<monad::execution::TransactionStatus>()
                              : monad::execution::TransactionStatus::SUCCESS;
        }
    };

    template <>
    struct adl_serializer<monad::BlockHeader>
    {
        static void from_json(nlohmann::json const &json, monad::BlockHeader &o)
        {
            o.parent_hash = json["previousHash"].get<monad::bytes32_t>();
            o.difficulty = json["currentDifficulty"].get<monad::uint256_t>();
            o.number = static_cast<uint64_t>(
                json["currentNumber"].get<monad::uint256_t>());
            o.gas_limit = static_cast<uint64_t>(
                json["currentGasLimit"].get<monad::uint256_t>());
            o.timestamp = static_cast<uint64_t>(
                json["currentTimestamp"].get<monad::uint256_t>());
            o.beneficiary = json["currentCoinbase"].get<monad::address_t>();

            // we cannot use the nlohmann::json from_json<uint64_t> because
            // it does not use the strtoull implementation, whereas we need
            // it so we can turn a hex string into a uint64_t
            o.base_fee_per_gas =
                json.contains("currentBaseFee")
                    ? std::make_optional<uint64_t>(
                          integer_from_json<uint64_t>(json["currentBaseFee"]))
                    : std::nullopt;

            o.prev_randao = json["currentRandom"].get<monad::bytes32_t>();
        }
    };
}
