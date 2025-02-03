#include <monad/chain/chain_config.h>
#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/chain/monad_devnet.hpp>
#include <monad/chain/monad_testnet.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/switch_evmc_revision.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/rpc/eth_call.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>
#include <monad/types/incarnation.hpp>

#include <boost/outcome/try.hpp>

#include <quill/Quill.h>

#include <filesystem>
#include <vector>

using namespace monad;

namespace
{
    template <evmc_revision rev>
    Result<evmc::Result> eth_call_impl(
        Chain const &chain, Transaction const &txn, BlockHeader const &header,
        uint64_t const block_number, Address const &sender, TrieDb &tdb,
        BlockHashBufferFinalized &buffer,
        monad_state_override_set const &state_overrides)
    {
        Transaction enriched_txn{txn};

        // SignatureAndChain validation hacks
        enriched_txn.sc.chain_id = chain.get_chain_id();
        enriched_txn.sc.r = 1;
        enriched_txn.sc.s = 1;

        BOOST_OUTCOME_TRY(static_validate_transaction<rev>(
            enriched_txn, header.base_fee_per_gas, chain.get_chain_id()));

        tdb.set_block_and_round(block_number, std::nullopt);
        BlockState block_state{tdb};
        // avoid conflict with block reward txn
        Incarnation incarnation{block_number, Incarnation::LAST_TX - 1u};
        State state{block_state, incarnation};

        for (auto const &[addr, state_delta] : state_overrides.override_sets) {
            // address
            Address address{};
            std::memcpy(address.bytes, addr.data(), sizeof(Address));

            // This would avoid seg-fault on storage override for non-existing
            // accounts
            auto const &account = state.recent_account(address);
            if (MONAD_UNLIKELY(!account.has_value())) {
                state.create_contract(address);
            }

            if (state_delta.balance.has_value()) {
                auto const balance = intx::be::unsafe::load<uint256_t>(
                    state_delta.balance.value().data());
                if (balance >
                    intx::be::load<uint256_t>(state.get_balance(address))) {
                    state.add_to_balance(
                        address,
                        balance - intx::be::load<uint256_t>(
                                      state.get_balance(address)));
                }
                else {
                    state.subtract_from_balance(
                        address,
                        intx::be::load<uint256_t>(state.get_balance(address)) -
                            balance);
                }
            }

            if (state_delta.nonce.has_value()) {
                state.set_nonce(address, state_delta.nonce.value());
            }

            if (state_delta.code.has_value()) {
                byte_string const code{
                    state_delta.code.value().data(),
                    state_delta.code.value().size()};
                state.set_code(address, code);
            }

            auto update_state =
                [&](std::map<std::vector<uint8_t>, std::vector<uint8_t>> const
                        &diff) {
                    for (auto const &[key, value] : diff) {
                        bytes32_t storage_key;
                        bytes32_t storage_value;
                        std::memcpy(
                            storage_key.bytes, key.data(), sizeof(bytes32_t));
                        std::memcpy(
                            storage_value.bytes,
                            value.data(),
                            sizeof(bytes32_t));

                        state.set_storage(address, storage_key, storage_value);
                    }
                };

            // Remove single storage
            if (!state_delta.state_diff.empty()) {
                // we need to access the account first before accessing its
                // storage
                (void)state.get_nonce(address);
                update_state(state_delta.state_diff);
            }

            // Remove all override
            if (!state_delta.state.empty()) {
                state.set_to_state_incarnation(address);
                update_state(state_delta.state);
            }
        }

        // nonce validation hack
        auto const &acct = state.recent_account(sender);
        enriched_txn.nonce = acct.has_value() ? acct.value().nonce : 0;

        BOOST_OUTCOME_TRY(validate_transaction(enriched_txn, acct));
        auto const tx_context = get_tx_context<rev>(
            enriched_txn, sender, header, chain.get_chain_id());
        NoopCallTracer call_tracer;
        EvmcHost<rev> host{call_tracer, tx_context, buffer, state};
        return execute_impl_no_validation<rev>(
            state,
            host,
            enriched_txn,
            sender,
            header.base_fee_per_gas.value_or(0),
            header.beneficiary);
    }

    Result<evmc::Result> eth_call_impl(
        Chain const &chain, evmc_revision const rev, Transaction const &txn,
        BlockHeader const &header, uint64_t const block_number,
        Address const &sender, TrieDb &tdb, BlockHashBufferFinalized &buffer,
        monad_state_override_set const &state_overrides)
    {
        SWITCH_EVMC_REVISION(
            eth_call_impl,
            chain,
            txn,
            header,
            block_number,
            sender,
            tdb,
            buffer,
            state_overrides);
        MONAD_ASSERT(false);
    }

}

namespace monad
{
    quill::Logger *tracer = nullptr;
}

int monad_evmc_result::get_status_code() const
{
    return status_code;
}

std::vector<uint8_t> monad_evmc_result::get_output_data() const
{
    return output_data;
}

std::string monad_evmc_result::get_message() const
{
    return message;
}

int64_t monad_evmc_result::get_gas_used() const
{
    return gas_used;
}

int64_t monad_evmc_result::get_gas_refund() const
{
    return gas_refund;
}

void monad_state_override_set::add_override_address(bytes const &address)
{
    MONAD_ASSERT(override_sets.find(address) == override_sets.end());
    MONAD_ASSERT(address.size() == sizeof(Address));
    override_sets.emplace(address, monad_state_override_object());
}

void monad_state_override_set::set_override_balance(
    bytes const &address, bytes const &balance)
{
    MONAD_ASSERT(override_sets.find(address) != override_sets.end());
    MONAD_ASSERT(address.size() == sizeof(Address));
    override_sets[address].balance = balance;
}

void monad_state_override_set::set_override_nonce(
    bytes const &address, uint64_t const &nonce)
{
    MONAD_ASSERT(override_sets.find(address) != override_sets.end());
    MONAD_ASSERT(address.size() == sizeof(Address));
    override_sets[address].nonce = nonce;
}

void monad_state_override_set::set_override_code(
    bytes const &address, bytes const &code)
{
    MONAD_ASSERT(override_sets.find(address) != override_sets.end());
    MONAD_ASSERT(address.size() == sizeof(Address));
    override_sets[address].code = code;
}

void monad_state_override_set::set_override_state_diff(
    bytes const &address, bytes const &key, bytes const &value)
{
    MONAD_ASSERT(override_sets.find(address) != override_sets.end());
    MONAD_ASSERT(address.size() == sizeof(Address));
    auto &object = override_sets[address].state_diff;
    MONAD_ASSERT(object.find(key) == object.end());
    MONAD_ASSERT(key.size() == sizeof(bytes32_t));
    object.emplace(key, value);
}

void monad_state_override_set::set_override_state(
    bytes const &address, bytes const &key, bytes const &value)
{
    MONAD_ASSERT(override_sets.find(address) != override_sets.end());
    MONAD_ASSERT(address.size() == sizeof(Address));
    auto &object = override_sets[address].state;
    MONAD_ASSERT(object.find(key) == object.end());
    MONAD_ASSERT(key.size() == sizeof(bytes32_t));
    object.emplace(key, value);
}

// TODO: eth_call should take in a handle to db instead
monad_evmc_result eth_call(
    monad_chain_config const chain_config, std::vector<uint8_t> const &rlp_tx,
    std::vector<uint8_t> const &rlp_header,
    std::vector<uint8_t> const &rlp_sender, uint64_t const block_number,
    std::string const &triedb_path,
    monad_state_override_set const &state_overrides)
{
    byte_string_view rlp_tx_view(rlp_tx.begin(), rlp_tx.end());
    auto const tx_result = rlp::decode_transaction(rlp_tx_view);
    MONAD_ASSERT(!tx_result.has_error());
    MONAD_ASSERT(rlp_tx_view.empty());
    auto const tx = tx_result.value();

    byte_string_view rlp_header_view(rlp_header.begin(), rlp_header.end());
    auto const block_header_result = rlp::decode_block_header(rlp_header_view);
    MONAD_ASSERT(rlp_header_view.empty());
    MONAD_ASSERT(!block_header_result.has_error());
    auto const block_header = block_header_result.value();

    byte_string_view rlp_sender_view(rlp_sender.begin(), rlp_sender.end());
    auto const sender_result = rlp::decode_address(rlp_sender_view);
    MONAD_ASSERT(rlp_sender_view.empty());
    MONAD_ASSERT(!sender_result.has_error());
    auto const sender = sender_result.value();

    std::vector<std::filesystem::path> paths;
    if (std::filesystem::is_directory(triedb_path)) {
        for (auto const &file :
             std::filesystem::directory_iterator(triedb_path)) {
            paths.emplace_back(file.path());
        }
    }
    else {
        paths.emplace_back(triedb_path);
    }

    // rodb is not thread safe
    thread_local mpt::Db db{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = paths}};
    thread_local TrieDb tdb{db};

    monad_evmc_result ret{};
    BlockHashBufferFinalized buffer{};
    if (!init_block_hash_buffer_from_triedb(db, block_number, buffer)) {
        ret.status_code = EVMC_REJECTED;
        ret.message = "failure to initialize block hash buffer";
        return ret;
    }

    auto chain = [chain_config] -> std::unique_ptr<Chain> {
        switch (chain_config) {
        case CHAIN_CONFIG_ETHEREUM_MAINNET:
            return std::make_unique<EthereumMainnet>();
        case CHAIN_CONFIG_MONAD_DEVNET:
            return std::make_unique<MonadDevnet>();
        case CHAIN_CONFIG_MONAD_TESTNET:
            return std::make_unique<MonadTestnet>();
        }
        MONAD_ASSERT(false);
    }();

    evmc_revision const rev =
        chain->get_revision(block_header.number, block_header.timestamp);

    auto const result = eth_call_impl(
        *chain,
        rev,
        tx,
        block_header,
        block_number,
        sender,
        tdb,
        buffer,
        state_overrides);
    if (MONAD_UNLIKELY(result.has_error())) {
        ret.status_code = EVMC_REJECTED;
        ret.message = result.error().message().c_str();
    }
    else {
        auto const &res = result.assume_value();
        ret.status_code = res.status_code;
        ret.output_data = {res.output_data, res.output_data + res.output_size};
        ret.gas_used = static_cast<int64_t>(tx.gas_limit) - res.gas_left;
        ret.gas_refund = res.gas_refund;
    }
    return ret;
}
