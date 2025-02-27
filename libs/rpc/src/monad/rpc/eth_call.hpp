#pragma once

#include <monad/chain/chain_config.h>

#include <cstdint>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <vector>

struct monad_evmc_result
{
    int status_code{};
    std::vector<uint8_t> output_data{};
    std::string message{};
    int64_t gas_used{};
    int64_t gas_refund{};

    int get_status_code() const;
    std::vector<uint8_t> get_output_data() const;
    std::string get_message() const;
    int64_t get_gas_used() const;
    int64_t get_gas_refund() const;
};

struct monad_state_override_set
{
    using bytes = std::vector<uint8_t>;

    struct monad_state_override_object
    {
        std::optional<bytes> balance{std::nullopt};
        std::optional<uint64_t> nonce{std::nullopt};
        std::optional<bytes> code{std::nullopt};
        std::map<bytes, bytes> state{};
        std::map<bytes, bytes> state_diff{};
    };

    std::map<bytes, monad_state_override_object> override_sets;

    // autocxx doesn't understand default constructor, so explicity declare here
    monad_state_override_set() {}

    void add_override_address(bytes const &address);

    void set_override_balance(bytes const &address, bytes const &balance);

    void set_override_nonce(bytes const &address, uint64_t const &nonce);

    void set_override_code(bytes const &address, bytes const &code);

    void set_override_state_diff(
        bytes const &address, bytes const &key, bytes const &value);

    void set_override_state(
        bytes const &address, bytes const &key, bytes const &value);
};

monad_evmc_result eth_call(
    monad_chain_config, std::vector<uint8_t> const &rlp_txn,
    std::vector<uint8_t> const &rlp_header,
    std::vector<uint8_t> const &rlp_sender, uint64_t const block_number,
    uint64_t const block_round, std::string const &triedb_path,
    monad_state_override_set const &state_overrides, bool is_latest);
