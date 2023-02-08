#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

MONAD_NAMESPACE_BEGIN

struct BlockHeader {
    /* glee for shea: existing representation? */
    /* self note: `byte_string_fixed` */
    using NonceType = std::array<uint8_t, 8>;

    bytes32_t parent_hash{};
    bytes32_t ommers_hash{};
    address_t beneficiary{};
    bytes32_t state_root{};
    bytes32_t transactions_root{};
    bytes32_t receipts_root{};
    Receipt::Bloom logs_bloom{};
    uint256_t difficulty{};
    uint64_t number{0};
    uint64_t gas_limit{0};
    uint64_t gas_used{0};
    uint64_t timestamp{0};

    byte_string extra_data{};

    bytes32_t mix_hash{};
    NonceType nonce{};

    std::optional<uint256_t> base_fee_per_gas{std::nullopt};  // EIP-1559
};

struct BlockBody {
    std::vector<Transaction> transactions;
    std::vector<BlockHeader> ommers;
};

struct Block : public BlockBody {
    BlockHeader header;
};

struct BlockWithHash {
    Block block;
    bytes32_t hash;
};

MONAD_NAMESPACE_END
