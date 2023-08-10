// Modifications to the Original Code (or portions thereof):
// Monad: 2023
// - Fit naming and type conventions of Monad
// Original Code is licensed under the Apache 2.0 License
// monad: Fast Ethereum Virtual Machine implementation
// Copyright 2022 The monad Authors.
// SPDX-License-Identifier: Apache-2.0
#pragma once

#include <boost/mp11.hpp>
#include <ethash/hash_types.hpp>
#include <filesystem>
#include <gtest/gtest.h>
#include <monad/core/transaction.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/ethereum/genesis.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/evmone_baseline_interpreter.hpp>
#include <monad/execution/instruction_tracer.hpp>
#include <monad/execution/static_precompiles.hpp>
#include <monad/execution/test/fakes.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/logging/monad_log.hpp>
#include <monad/state/account_state.hpp>
#include <monad/state/code_state.hpp>
#include <monad/state/state.hpp>
#include <monad/state/value_state.hpp>
#include <nlohmann/json.hpp>
#include <vector>

namespace fs = std::filesystem;
namespace json = nlohmann;

namespace monad::test
{

    using account_store_db_t = monad::db::InMemoryTrieDB;
    using code_db_t = std::unordered_map<monad::bytes32_t, monad::byte_string>;
    using state_t = monad::state::State<
        monad::state::AccountState<account_store_db_t>,
        monad::state::ValueState<account_store_db_t>,
        monad::state::CodeState<code_db_t>, monad::db::BlockDb,
        account_store_db_t>;
    using working_state_t =
        decltype(std::declval<state_t>().get_new_changeset(0u));

    struct TestMultiTransaction : monad::Transaction
    {
        struct Indexes
        {
            size_t input = 0;
            size_t gas_limit = 0;
            size_t value = 0;
        };

        std::vector<monad::Transaction::AccessList> access_lists_;
        std::vector<monad::byte_string> inputs_;
        std::vector<int64_t> gas_limits_;
        std::vector<intx::uint128> values_;

        [[nodiscard]] Transaction get(Indexes const &indexes) const noexcept
        {
            Transaction tx{*this};
            if (!access_lists_.empty())
                tx.access_list = access_lists_.at(indexes.input);
            tx.data = inputs_.at(indexes.input);
            tx.gas_limit = gas_limits_.at(indexes.gas_limit);
            tx.amount = values_.at(indexes.value);
            return tx;
        }
    };

    struct Case
    {
        struct Expectation
        {
            TestMultiTransaction::Indexes indexes_;
            monad::bytes32_t state_hash_;
            monad::bytes32_t logs_hash_;
            bool exception_{false};
        };

        size_t fork_index;
        std::vector<Expectation> expectations;
    };

    template <typename TState>
    struct StateTransitionTest
    {
        TState pre_state_;
        monad::BlockHeader block_;
        TestMultiTransaction multi_tx_;
        std::vector<Case> cases_;
        std::unordered_map<uint64_t, std::string> input_labels_;
    };

    template <typename T>
    T from_json(json::json const &j) = delete;

    template <>
    inline uint64_t from_json<uint64_t>(json::json const &j);

    template <>
    int64_t from_json<int64_t>(json::json const &j);

    template <>
    inline monad::address_t from_json(nlohmann::json const &json)
    {
        return evmc::from_hex<monad::address_t>(json.get<std::string>())
            .value();
    }

    template <>
    inline monad::uint256_t from_json(nlohmann::json const &json)
    {
        return intx::from_string<monad::uint256_t>(json.get<std::string>());
    }

    template <>
    inline uint128_t from_json(nlohmann::json const &json)
    {
        return intx::from_string<uint128_t>(json.get<std::string>());
    }

    template <>
    inline monad::byte_string from_json(nlohmann::json const &json)
    {
        return evmc::from_hex(json.get<std::string>()).value();
    }

    namespace json = nlohmann;
    using evmc::from_hex;

    template <>
    inline uint8_t from_json<uint8_t>(json::json const &j)
    {
        auto const ret = std::stoul(j.get<std::string>(), nullptr, 16);
        if (ret > std::numeric_limits<uint8_t>::max())
            throw std::out_of_range("from_json<uint8_t>: value > 0xFF");

        return static_cast<uint8_t>(ret);
    }

    template <typename T>
    static std::optional<T> integer_from_json(json::json const &j)
    {
        if (j.is_number_integer())
            return j.get<T>();

        if (!j.is_string())
            return {};

        auto const s = j.get<std::string>();
        size_t num_processed = 0;
        T v = 0;
        if constexpr (std::is_same_v<T, uint64_t>)
            v = std::stoull(s, &num_processed, 0);
        else
            v = std::stoll(s, &num_processed, 0);

        if (num_processed == 0 || num_processed != s.size())
            return {};
        return v;
    }

    template <>
    inline int64_t from_json<int64_t>(json::json const &j)
    {
        auto const v = integer_from_json<int64_t>(j);
        if (!v.has_value())
            throw std::invalid_argument(
                "from_json<int64_t>: must be integer or string of integer");
        return *v;
    }

    template <>
    inline uint64_t from_json<uint64_t>(json::json const &j)
    {
        auto const v = integer_from_json<uint64_t>(j);
        if (!v.has_value())
            throw std::invalid_argument(
                "from_json<uint64_t>: must be integer or string of integer");
        return *v;
    }

    template <>
    inline monad::bytes32_t from_json(json::json const &j)
    {
        // Special case to handle "0". Required by exec-spec-tests.
        // TODO: Get rid of it.
        if (j.is_string() && (j == "0" || j == "0x0"))
            return 0x00_bytes32;
        else
            return evmc::from_hex<monad::bytes32_t>(j.get<std::string>())
                .value();
    }

    /// Load common parts of Transaction or TestMultiTransaction.
    static void from_json_tx_common(json::json const &j, monad::Transaction &o)
    {
        o.from = from_json<evmc::address>(j.at("sender"));

        if (auto const to_it = j.find("to");
            to_it != j.end() && !to_it->get<std::string>().empty())
            o.to = from_json<evmc::address>(*to_it);

        if (auto const gas_price_it = j.find("gasPrice");
            gas_price_it != j.end()) {
            o.type = monad::Transaction::Type::eip155;
            o.gas_price = from_json<uint64_t>(*gas_price_it);
            o.priority_fee = o.gas_price;
            if (j.contains("maxFeePerGas") ||
                j.contains("maxPriorityFeePerGas")) {
                throw std::invalid_argument("invalid transaction: contains "
                                            "both legacy and EIP-1559 fees");
            }
        }
        else {
            o.type = monad::Transaction::Type::eip1559;
            o.gas_price = from_json<uint64_t>(j.at("maxFeePerGas"));
            o.priority_fee = from_json<uint64_t>(j.at("maxPriorityFeePerGas"));
        }
    }

    // Based on calculateEIP1559BaseFee from ethereum/retesteth
    inline uint64_t calculate_current_base_fee_eip1559(
        uint64_t parent_gas_used, uint64_t parent_gas_limit,
        uint64_t parent_base_fee)
    {
        // TODO: Make sure that 64-bit precision is good enough.
        static constexpr auto BASE_FEE_MAX_CHANGE_DENOMINATOR = 8;
        static constexpr auto ELASTICITY_MULTIPLIER = 2;

        uint64_t base_fee = 0;

        auto const parent_gas_target = parent_gas_limit / ELASTICITY_MULTIPLIER;

        if (parent_gas_used == parent_gas_target)
            base_fee = parent_base_fee;
        else if (parent_gas_used > parent_gas_target) {
            auto const gas_used_delta = parent_gas_used - parent_gas_target;
            auto const formula = parent_base_fee * gas_used_delta /
                                 parent_gas_target /
                                 BASE_FEE_MAX_CHANGE_DENOMINATOR;
            auto const base_fee_per_gas_delta = formula > 1 ? formula : 1;
            base_fee = parent_base_fee + base_fee_per_gas_delta;
        }
        else {
            auto const gas_used_delta = parent_gas_target - parent_gas_used;

            auto const base_fee_per_gas_delta_u128 =
                intx::uint128(parent_base_fee, 0) *
                intx::uint128(gas_used_delta, 0) / parent_gas_target /
                BASE_FEE_MAX_CHANGE_DENOMINATOR;

            auto const base_fee_per_gas_delta = base_fee_per_gas_delta_u128[0];
            if (parent_base_fee > base_fee_per_gas_delta)
                base_fee = parent_base_fee - base_fee_per_gas_delta;
            else
                base_fee = 0;
        }
        return base_fee;
    }

    static inline std::optional<size_t> to_fork_index(std::string_view s)
    {
        if (s == "Frontier")
            return 0;
        if (s == "Homestead")
            return 1;
        if (s == "EIP158")
            return 2;
        if (s == "Byzantium")
            return 3;
        if (s == "Constantinople")
            return 4;
        if (s == "Istanbul")
            return 5;
        if (s == "Berlin")
            return 6;
        if (s == "London")
            return 7;
        return std::nullopt;
    }

    template <typename EnumT>
    inline constexpr auto to_underlying(EnumT e) noexcept
    {
        return static_cast<std::underlying_type_t<EnumT>>(e);
    }
    template <typename TState>
    void load_state_from_json(json::json const &j, TState &state)
    {
        for (auto const &[j_addr, j_acc] : j.items()) {
            auto const account_address = from_json<monad::address_t>(j_addr);
            state.create_account(account_address);
            if (j_acc.contains("code")) {
                state.set_code(
                    account_address,
                    from_json<monad::byte_string>(j_acc.at("code")));
            }

            state.set_balance(
                account_address, from_json<intx::uint256>(j_acc.at("balance")));
            state.set_nonce(
                account_address, from_json<uint64_t>(j_acc.at("nonce")));

            if (j_acc.contains("storage") && j_acc["storage"].is_object()) {
                for (auto const &[key, value] : j_acc["storage"].items()) {
                    auto const key_int =
                        intx::bswap(intx::from_string<monad::uint256_t>(key));
                    auto const value_int =
                        intx::bswap(intx::from_string<monad::uint256_t>(
                            value.get<std::string>()));

                    monad::bytes32_t key_bytes32 =
                        *reinterpret_cast<monad::bytes32_t const *>(
                            as_words(key_int));
                    monad::bytes32_t value_bytes32 =
                        *reinterpret_cast<monad::bytes32_t const *>(
                            as_words(value_int));
                    (void)state.set_storage(
                        account_address, key_bytes32, value_bytes32);
                }
            }
        }
    }
    template <>
    inline monad::Transaction::AccessList
    from_json<monad::Transaction::AccessList>(json::json const &j)
    {
        monad::Transaction::AccessList o;
        for (auto const &a : j) {
            std::vector<monad::bytes32_t> storage_access_list;
            for (auto const &storage_key : a.at("storageKeys"))
                storage_access_list.emplace_back(
                    from_json<monad::bytes32_t>(storage_key));
            o.emplace_back(
                from_json<monad::address_t>(a.at("address")),
                std::move(storage_access_list));
        }
        return o;
    }

    static void from_json(json::json const &j, TestMultiTransaction &o)
    {
        from_json_tx_common(j, o);

        for (auto const &j_data : j.at("data"))
            o.inputs_.emplace_back(from_json<monad::byte_string>(j_data));

        if (auto const ac_it = j.find("accessLists"); ac_it != j.end()) {
            for (auto const &j_access_list : *ac_it)
                o.access_lists_.emplace_back(
                    from_json<monad::Transaction::AccessList>(j_access_list));
            if (o.type ==
                monad::Transaction::Type::eip155) // Upgrade tx type if tx has
                                                  // access lists
                o.type = monad::Transaction::Type::eip2930;
        }

        for (auto const &j_gas_limit : j.at("gasLimit"))
            o.gas_limits_.emplace_back(from_json<int64_t>(j_gas_limit));

        for (auto const &j_value : j.at("value"))
            o.values_.emplace_back(from_json<intx::uint256>(j_value));
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

    static void from_json(json::json const &j, TestMultiTransaction::Indexes &o)
    {
        o.input = j.at("data").get<size_t>();
        o.gas_limit = j.at("gas").get<size_t>();
        o.value = j.at("value").get<size_t>();
    }

    static void from_json(json::json const &j, Case::Expectation &o)
    {
        o.indexes_ = j.at("indexes").get<TestMultiTransaction::Indexes>();
        o.state_hash_ = from_json<monad::bytes32_t>(j.at("hash"));
        o.logs_hash_ = from_json<monad::bytes32_t>(j.at("logs"));
        o.exception_ = j.contains("expectException");
    }

    template <typename TState>
    void load_state_test(
        StateTransitionTest<TState> &s, std::ifstream &f,
        std::string suite_name, std::string test_name, std::string file_name)
    {
        auto const j = nlohmann::json::parse(f);
        if (!j.is_object() || j.empty())
            throw std::invalid_argument{"JSON test must be an object with "
                                        "single key of the test name"};

        auto const &j_t =
            *j.begin(); // Content is in a dict with the test name.

        load_state_from_json(j_t.at("pre"), s.pre_state_);

        s.multi_tx_ = j_t.at("transaction").get<TestMultiTransaction>();
        s.block_ = beneficiary_from_json(s.pre_state_, j_t.at("env"));

        if (auto const &info = j_t.at("_info"); info.contains("labels")) {
            for (auto const &[j_id, j_label] : info.at("labels").items())
                s.input_labels_.emplace(from_json<uint64_t>(j_id), j_label);
        }

        int index = 0;
        for (auto const &[rev_name, expectations] : j_t.at("post").items()) {
            // TODO(c++20): Use emplace_back with aggregate initialization.
            auto maybe_fork_index = to_fork_index(rev_name);
            if (!maybe_fork_index) {
                MONAD_LOG_WARNING(
                    quill::get_logger(),
                    "skipping post index {} in {}:{}:{} due to invalid fork "
                    "index {}",
                    index++,
                    suite_name,
                    test_name,
                    file_name,
                    rev_name);
                continue;
            }
            s.cases_.push_back(
                {maybe_fork_index.value(),
                 expectations.get<std::vector<Case::Expectation>>()});
        }
    }

    template <typename TFork>
    using interpreter_t =
        monad::execution::EVMOneBaselineInterpreter<working_state_t, TFork>;

    template <typename TFork>
    using transaction_processor_t =
        monad::execution::TransactionProcessor<working_state_t, TFork>;

    template <typename TFork>
    using static_precompiles_t = monad::execution::StaticPrecompiles<
        working_state_t, TFork, typename TFork::static_precompiles_t>;

    template <typename TFork>
    using evm_t = monad::execution::Evm<
        working_state_t, TFork, static_precompiles_t<TFork>,
        interpreter_t<TFork>>;

    template <typename TFork>
    using host_t =
        monad::execution::EvmcHost<working_state_t, TFork, evm_t<TFork>>;

    using namespace boost::mp11;
    using namespace monad::fork_traits;

    template <typename T>
    constexpr auto Traverse()
    {
        if constexpr (requires { typename T::next_fork_t; }) {
            return boost::mp11::mp_push_front<
                decltype(Traverse<typename T::next_fork_t>()),
                T>{};
        }
        else {
            return boost::mp11::mp_list<T>{};
        }
    }

    template <>
    constexpr auto Traverse<no_next_fork_t>()
    {
        return boost::mp11::mp_list<no_next_fork_t>{};
    }

    using all_forks_t = decltype(Traverse<monad::fork_traits::frontier>());
    static_assert(mp_size<all_forks_t>::value == 8);

    template <typename TFork>
    struct Execution
    {
        Execution(
            monad::BlockHeader const &block_header,
            monad::Transaction const &transaction, working_state_t &state)
            : host_{block_header, transaction, state}
            , transaction_processor_{}
        {
        }

        monad::Receipt
        execute(working_state_t &state, monad::Transaction const &transaction)
        {
            using Status = typename transaction_processor_t<TFork>::Status;
            typename decltype(transaction_processor_)::Status status =
                transaction_processor_.validate(
                    state,
                    transaction,
                    host_.block_header_.base_fee_per_gas.value_or(0));
            if (status != Status::SUCCESS) {
                //            throw std::runtime_error("properly handle invalid
                //            transactions");
            }
            return transaction_processor_.execute(
                state,
                host_,
                transaction,
                host_.block_header_.base_fee_per_gas.value_or(0));
        }

        host_t<TFork> host_;
        transaction_processor_t<TFork> transaction_processor_;
    };

    // creates a sum type over all the forks:
    // std::variant<std::monostate, Execution<frontier>, Execution<homestead>,
    // ...>
    using execution_variant =
        decltype([]<typename... Types>(boost::mp11::mp_list<Types...>) {
            return std::variant<std::monostate, Types...>{};
        }(mp_transform<Execution, all_forks_t>{}));

    /**
     * execute a transaction with a given state using a fork specified at
     * runtime
     * @param fork_index
     * @param state
     * @param transaction
     * @return a receipt of the transaction
     */
    inline monad::Receipt execute(
        size_t fork_index, monad::BlockHeader const &block_header,
        working_state_t &state, monad::Transaction const &transaction)
    {
        using boost::mp11::mp_list;
        // makes a glorified jump table by creating an array where the i'th
        // index corresponds to an instance of the Execution struct with the
        // i'th fork injected.
        auto execution_array = []<typename... Ts>(
                                   mp_list<Ts...>,
                                   monad::BlockHeader const &block_header,
                                   working_state_t &state,
                                   monad::Transaction const &transaction) {
            return std::array<execution_variant, sizeof...(Ts)>{
                Execution<Ts>{block_header, transaction, state}...};
        }(all_forks_t{}, block_header, state, transaction);

        // we then dispatch into the appropriate fork at runtime using std::get
        auto &variant = execution_array.at(fork_index);

        std::optional<monad::Receipt> maybe_receipt;
        mp_for_each<mp_iota_c<mp_size<all_forks_t>::value>>([&](auto I) {
            if (I == fork_index) {
                maybe_receipt =
                    std::get<Execution<mp_at_c<all_forks_t, I>>>(variant)
                        .execute(state, transaction);
            }
        });

        return maybe_receipt.value();
    }

    template <typename TState>
    void run_state_test(StateTransitionTest<TState> &test, evmc::VM &vm)
    {
        for (auto const &[rev, cases] : test.cases_) {
            for (size_t case_index = 0; case_index != cases.size();
                 ++case_index) {
                auto const &expected = cases[case_index];
                auto const tx = test.multi_tx_.get(expected.indexes_);
                auto receipt = execute(rev, test.block_, test.pre_state_, tx);

                auto const rlp_encoded_transaction =
                    monad::rlp::encode_transaction(tx);
                auto const transaction_hash = ethash_keccak256(
                    rlp_encoded_transaction.data(),
                    rlp_encoded_transaction.size());
                auto const transaction_hash_byte_string = monad::byte_string{
                    reinterpret_cast<uint8_t const *>(transaction_hash.bytes),
                    32};

                // TODO: assert something about receipt status?
                // assert(receipt.status);
            }
        }
    }

} // namespace monad::test
