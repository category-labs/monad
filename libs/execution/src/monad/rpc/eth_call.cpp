#include <monad/core/block.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/rpc/eth_call.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

#include <boost/outcome/config.hpp>
#include <boost/outcome/try.hpp>

MONAD_RPC_NAMESPACE_BEGIN

/*
    For eth_call with real txn, submit as it is
    For eth_call with only "from" "to" and "data", set txn.value = 0 & gas_limit
    to a big number to guarantee success on txn side if no "from", set from =
    "0x0000...00"
*/

evmc_result eth_call(
    std::vector<uint8_t> const &rlp_encoded_transaction,
    std::vector<uint8_t> const &rlp_encoded_block_header,
    std::vector<uint8_t> const &rlp_encoded_sender, uint64_t const block_number,
    std::string const &trie_db_path, std::string const &block_db_path)
{

    byte_string_view encoded_transaction(
        rlp_encoded_transaction.begin(), rlp_encoded_transaction.end());
    auto const txn_result = rlp::decode_transaction(encoded_transaction);
    MONAD_ASSERT(!txn_result.has_error());
    MONAD_ASSERT(encoded_transaction.empty());
    auto const txn = txn_result.value();

    byte_string_view encoded_block_header(
        rlp_encoded_block_header.begin(), rlp_encoded_block_header.end());
    auto const block_header_result =
        rlp::decode_block_header(encoded_block_header);
    MONAD_ASSERT(encoded_block_header.empty());
    MONAD_ASSERT(!block_header_result.has_error());
    auto const block_header = block_header_result.value();

    byte_string_view encoded_sender(
        rlp_encoded_sender.begin(), rlp_encoded_sender.end());
    auto const sender_result = rlp::decode_address(encoded_sender);
    MONAD_ASSERT(encoded_sender.empty());
    MONAD_ASSERT(!sender_result.has_error());
    auto const sender = sender_result.value();

    BlockHashBuffer buffer{};
    uint64_t start_block_number = block_number < 256 ? 1 : block_number - 255;
    BlockDb block_db{block_db_path.c_str()};

    while (start_block_number < block_number) {
        Block block{};
        bool const result = block_db.get(start_block_number, block);
        MONAD_ASSERT(result);
        buffer.set(start_block_number - 1, block.header.parent_hash);
        ++start_block_number;
    }

    // TODO: construct trie_db_path properly
    auto result = eth_call_helper(
        txn,
        block_header,
        block_number,
        sender,
        buffer,
        {trie_db_path.c_str()});
    if (MONAD_UNLIKELY(result.has_error())) {
        // TODO: If validation fails, just return as generic failure for now
        evmc_result res{};
        res.status_code = EVMC_FAILURE;
        return res;
    }

    return result.value().release_raw();
}

Result<evmc::Result> eth_call_helper(
    Transaction const &txn, BlockHeader const &header,
    uint64_t const block_number, Address const &sender,
    BlockHashBuffer const &buffer,
    std::vector<std::filesystem::path> const &dbname_paths,
    nlohmann::json const &state_overrides)
{
    // TODO: Hardset rev to be Shanghai at the moment
    static constexpr auto rev = EVMC_SHANGHAI;
    Transaction enriched_txn{txn};

    // SignatureAndChain validation hacks
    enriched_txn.sc.chain_id = 1;
    enriched_txn.sc.r = 1;
    enriched_txn.sc.s = 1;

    BOOST_OUTCOME_TRY(
        static_validate_transaction<rev>(enriched_txn, header.base_fee_per_gas))

    TrieDb ro{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = dbname_paths}};
    ro.set_block_number(block_number);
    ro.load_latest();
    BlockState block_state{ro};
    State state{block_state, Incarnation{0, 0}};

    // State override
    for (auto const &[addr, state_delta] : state_overrides.items()) {
        // address
        Address address{};
        auto const address_byte_string = evmc::from_hex(addr);
        MONAD_ASSERT(address_byte_string.has_value());
        std::copy_n(
            address_byte_string.value().begin(),
            address_byte_string.value().length(),
            address.bytes);

        if (state_delta.contains("balance")) {
            auto const balance =
                intx::from_string<uint256_t>(state_delta.at("balance"));
            if (balance >
                intx::be::load<uint256_t>(state.get_balance(address))) {
                state.add_to_balance(
                    address,
                    balance -
                        intx::be::load<uint256_t>(state.get_balance(address)));
            }
            else {
                state.subtract_from_balance(
                    address,
                    intx::be::load<uint256_t>(state.get_balance(address)) -
                        balance);
            }
        }

        if (state_delta.contains("nonce")) {
            auto const nonce = state_delta.at("nonce").get<uint64_t>();
            state.set_nonce(address, nonce);
        }

        if (state_delta.contains("code")) {
            auto const code =
                evmc::from_hex(state_delta.at("code").get<std::string>())
                    .value();
            state.set_code(address, code);
        }

        // storage is called "state"
        if (state_delta.contains("state")) {
            for (auto const &[k, v] : state_delta.at("state").items()) {
                bytes32_t storage_key;
                bytes32_t storage_value;
                std::memcpy(
                    storage_key.bytes, evmc::from_hex(k).value().data(), 32);

                auto const storage_value_byte_string =
                    evmc::from_hex("0x" + v.get<std::string>()).value();
                std::copy_n(
                    storage_value_byte_string.begin(),
                    storage_value_byte_string.length(),
                    storage_value.bytes);

                state.set_storage(address, storage_key, storage_value);
            }
        }
    }

    auto &acct = state.recent_account(sender);

    // nonce validation hack
    enriched_txn.nonce = acct.has_value() ? acct.value().nonce : 0;

    BOOST_OUTCOME_TRY(validate_transaction(enriched_txn, acct));
    auto const tx_context = get_tx_context<rev>(enriched_txn, sender, header);
    EvmcHost<rev> host{tx_context, buffer, state};
    return execute_impl_no_validation<rev>(
        state,
        host,
        enriched_txn,
        sender,
        header.base_fee_per_gas.value_or(0),
        header.beneficiary);
}

MONAD_RPC_NAMESPACE_END
