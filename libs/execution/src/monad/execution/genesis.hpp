#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/db.hpp>
#include <monad/state2/state_deltas.hpp>

#include <evmc/hex.hpp>

#include <nlohmann/json.hpp>

#include <intx/intx.hpp>

#include <algorithm>
#include <fstream>
#include <string>

MONAD_NAMESPACE_BEGIN

// TODO: Different chain_id has different genesis json file (with some of them
// not having certain field)
// Issue #131
inline BlockHeader read_genesis_blockheader(nlohmann::json const &genesis_json)
{
    BlockHeader block_header{};

    block_header.difficulty = intx::from_string<uint256_t>(
        genesis_json["difficulty"].get<std::string>());

    auto const extra_data =
        evmc::from_hex(genesis_json["extraData"].get<std::string>());
    MONAD_ASSERT(extra_data.has_value());
    block_header.extra_data = extra_data.value();

    block_header.gas_limit =
        std::stoull(genesis_json["gasLimit"].get<std::string>(), nullptr, 0);

    auto const mix_hash_byte_string =
        evmc::from_hex(genesis_json["mixHash"].get<std::string>());
    MONAD_ASSERT(mix_hash_byte_string.has_value());
    std::copy_n(
        mix_hash_byte_string.value().begin(),
        mix_hash_byte_string.value().length(),
        block_header.prev_randao.bytes);

    uint64_t const nonce{
        std::stoull(genesis_json["nonce"].get<std::string>(), nullptr, 0)};
    intx::be::unsafe::store<uint64_t>(block_header.nonce.data(), nonce);

    auto const parent_hash_byte_string =
        evmc::from_hex(genesis_json["parentHash"].get<std::string>());
    MONAD_ASSERT(parent_hash_byte_string.has_value());
    std::copy_n(
        parent_hash_byte_string.value().begin(),
        parent_hash_byte_string.value().length(),
        block_header.parent_hash.bytes);

    block_header.timestamp =
        std::stoull(genesis_json["timestamp"].get<std::string>(), nullptr, 0);

    return block_header;
}

inline void read_genesis_state(
    nlohmann::json const &genesis_json, StateDeltas &state_deltas)
{
    for (auto const &account_info : genesis_json["alloc"].items()) {
        Address address{};
        auto const address_byte_string =
            evmc::from_hex("0x" + account_info.key());
        MONAD_ASSERT(address_byte_string.has_value());
        std::copy_n(
            address_byte_string.value().begin(),
            address_byte_string.value().length(),
            address.bytes);

        Account account{};
        auto const balance_byte_string =
            account_info.value()["wei_balance"].get<std::string>();
        account.balance = intx::from_string<uint256_t>(balance_byte_string);
        account.nonce = 0u;

        state_deltas.emplace(
            address, StateDelta{.account = {std::nullopt, account}});
    }
}

inline BlockHeader
read_genesis(std::filesystem::path const &genesis_file, Db &db)
{
    std::ifstream ifile(genesis_file.c_str());
    auto const genesis_json = nlohmann::json::parse(ifile);
    auto block_header = read_genesis_blockheader(genesis_json);

    block_header.transactions_root = NULL_ROOT;
    block_header.receipts_root = NULL_ROOT;

    StateDeltas state_deltas;
    read_genesis_state(genesis_json, state_deltas);
    db.commit(state_deltas, Code{}, block_header);

    block_header.state_root = db.state_root();

    return block_header;
}

inline void verify_genesis(BlockDb &block_db, BlockHeader const &block_header)
{
    Block block{};
    bool const status = block_db.get(0u, block);
    MONAD_ASSERT(status);
    // There should be no txn/receipt for the genesis block, so just asserting
    // on state root for now
    MONAD_ASSERT(block_header.state_root == block.header.state_root);
}

inline void read_and_verify_genesis(
    BlockDb &block_db, Db &db, std::filesystem::path const &genesis_file_path)
{
    auto const block_header = read_genesis(genesis_file_path, db);
    verify_genesis(block_db, block_header);
}

MONAD_NAMESPACE_END
