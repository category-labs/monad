#pragma once

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

struct monad_evmc_result
{
    int status_code;
    std::vector<uint8_t> output_data;
    std::string message;
    int64_t gas_used;
    int64_t gas_refund;

    int get_status_code() const;
    std::vector<uint8_t> get_output_data() const;
    std::string get_message() const;
    int64_t get_gas_used() const;
    int64_t get_gas_refund() const;
};

monad_evmc_result eth_call(
    std::vector<uint8_t> const &rlp_txn, std::vector<uint8_t> const &rlp_header,
    std::vector<uint8_t> const &rlp_sender, uint64_t block_number,
    std::string const &triedb_path, std::string const &blockdb_path);
