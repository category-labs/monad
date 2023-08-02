#pragma once

#include <ethash/keccak.hpp>
#include <intx/intx.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/block_db.hpp>
#include <monad/execution/test/fakes.hpp>
#include <monad/logging/config.hpp>
#include <monad/logging/monad_log.hpp>
#include <nlohmann/json.hpp>
#include <string>
#include <test_resource_data.h>

namespace test
{
    using namespace evmc::literals;

    template <typename T>
    T from_json(nlohmann::json const &json) = delete;

    template <>
    monad::address_t from_json(nlohmann::json const &json)
    {
        return evmc::from_hex<monad::address_t>(json.get<std::string>())
            .value();
    }

    template <>
    monad::uint256_t from_json(nlohmann::json const &json)
    {
        return intx::from_string<monad::uint256_t>(json.get<std::string>());
    }

    template <>
    monad::uint128_t from_json(nlohmann::json const &json)
    {
        return intx::from_string<monad::uint128_t>(json.get<std::string>());
    }

    template <>
    monad::byte_string from_json(nlohmann::json const &json)
    {
        return evmc::from_hex(json.get<std::string>()).value();
    }

    template <typename TState>
    void from_json(TState &state, nlohmann::json const &json)
    {
        for (auto const &[address_string, account_json] : json.items()) {
            auto const account_address =
                from_json<monad::address_t>(address_string);
            auto const balance =
                from_json<monad::uint256_t>(account_json["balance"]);
            auto const nonce = static_cast<uint64_t>(
                from_json<monad::uint256_t>(account_json["nonce"]));

            state.create_account(account_address);

            if (account_json.contains("code")) {
                auto const code = from_json<monad::byte_string>(
                    account_json["code"].get<std::string>());
                state.set_code(account_address, code);
            }

            state.set_balance(account_address, balance);
            state.set_nonce(account_address, nonce);

            // TODO: parse the storage field
            if (account_json.contains("storage") &&
                account_json["storage"].is_object()) {
                for (auto const &[key, value] :
                     account_json["storage"].items()) {

                    auto const key_int =
                        intx::bswap(intx::from_string<monad::uint256_t>(key));
                    auto const value_int =
                        intx::bswap(intx::from_string<monad::uint256_t>(
                            value.get<std::string>()));

                    monad::bytes32_t key_bytes32 =
                        *reinterpret_cast<const monad::bytes32_t *>(
                            as_words(key_int));
                    monad::bytes32_t value_bytes32 =
                        *reinterpret_cast<const monad::bytes32_t *>(
                            as_words(value_int));
                    (void)state.set_storage(
                        account_address, key_bytes32, value_bytes32);
                }
            }
        }
    }

    std::string hex0x(const monad::address_t &a)
    {
        return "0x" + evmc::hex(a);
    }

    std::string hex0x(const monad::uint256_t &n)
    {
        return "0x" + intx::hex(n);
    }

    std::string hex0x(const monad::byte_string_view &n)
    {
        return "0x" + evmc::hex(n);
    }

    template <typename TState>
    nlohmann::json to_json(
        TState const &state,
        std::vector<monad::address_t> const &account_addresses)
    {
        auto res = nlohmann::json::object();

        for (auto const &account_address : account_addresses) {
            std::optional<monad::Account> const maybe_account =
                state.accounts_.db_.try_find(account_address);
            if (!maybe_account) {
                continue;
            }
            auto const &account = maybe_account.value();
            auto const &account_address_hex = hex0x(account_address);

            res[account_address_hex] = nlohmann::json::object();

            auto const code_string =
                hex0x(state.code_.code_at(account_address));
            if (code_string != "0x") {
                res[account_address_hex]["code"] = code_string;
            }

            res[account_address_hex]["balance"] = hex0x(account.balance);

            auto const nonce_string = hex0x(monad::uint256_t{account.nonce});
            if (nonce_string != "0x0") {
                res[account_address_hex]["nonce"] = nonce_string;
            }
        }

        return res;
    }

    template <>
    std::vector<monad::Transaction> from_json(nlohmann::json const &json)
    {
        [[maybe_unused]] auto const sender =
            from_json<monad::address_t>(json["sender"].get<std::string>());
        [[maybe_unused]] auto const to =
            from_json<monad::address_t>(json["to"].get<std::string>());
        auto const nonce =
            static_cast<uint64_t>(from_json<monad::uint256_t>(json["nonce"]));

        // TODO: kicking the transaction_type can down the road

        [[maybe_unused]] monad::Transaction::Type transaction_type;

        std::vector<monad::Transaction> res;

        size_t index = 0;
        for (auto const &data : json["data"]) {
            auto const transaction_data = from_json<monad::byte_string>(data);
            res.emplace_back(monad::Transaction{
                .nonce = nonce,
                .gas_price = static_cast<uint64_t>(
                    from_json<monad::uint256_t>(json["gasPrice"])),
                .gas_limit = static_cast<uint64_t>(
                    from_json<monad::uint256_t>(json["gasLimit"][0])),
                .amount = from_json<monad::uint128_t>(json["value"][index++]),
                .to = to,
                .from = sender,
                .data = transaction_data,
            });
        }

        return res;
    }

    template <class TState>
    monad::BlockHeader
    beneficiary_from_json(TState &s, nlohmann::json const &json)
    {
        auto const current_coinbase =
            from_json<monad::address_t>(json["currentCoinbase"]);
        auto const parent_hash_string =
            from_json<monad::byte_string>(json["previousHash"]);
        auto const parent_hash = *reinterpret_cast<monad::bytes32_t const *>(
            parent_hash_string.data());
        auto const difficulty =
            from_json<monad::uint256_t>(json["currentDifficulty"]);

        auto const number = static_cast<uint64_t>(
            from_json<monad::uint256_t>(json["currentNumber"]));

        auto const gas_limit = static_cast<uint64_t>(
            from_json<monad::uint256_t>(json["currentGasLimit"]));
        auto const timestamp = static_cast<uint64_t>(
            from_json<monad::uint256_t>(json["currentTimestamp"]));

        std::optional<uint64_t> maybe_base_fee_per_gas{std::nullopt};
        if (json.contains("currentBaseFee")) {
            maybe_base_fee_per_gas = static_cast<uint64_t>(
                from_json<monad::uint256_t>(json["currentBaseFee"]));
        }

        s.create_account(current_coinbase);

        return {
            .parent_hash = parent_hash,
            .difficulty = difficulty,
            .number = number,
            .gas_limit = gas_limit,
            .timestamp = timestamp,
            .beneficiary = current_coinbase,
            .base_fee_per_gas = maybe_base_fee_per_gas.value_or(0u)};
    }
}