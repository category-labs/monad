#include <monad/rpc/eth_call.hpp>

#include <monad/chain/monad_devnet.hpp>
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
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
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
    Result<evmc::Result> eth_call_impl(
        Transaction const &txn, BlockHeader const &header,
        uint64_t const block_number, Address const &sender,
        BlockHashBuffer const &buffer,
        std::vector<std::filesystem::path> const &dbname_paths,
        monad_state_override_set const &state_overrides)
    {
        constexpr evmc_revision rev = EVMC_SHANGHAI; // TODO
        MonadDevnet chain;
        MONAD_ASSERT(rev == chain.get_revision(header));

        Transaction enriched_txn{txn};

        // SignatureAndChain validation hacks
        enriched_txn.sc.chain_id = chain.get_chain_id();
        enriched_txn.sc.r = 1;
        enriched_txn.sc.s = 1;

        BOOST_OUTCOME_TRY(static_validate_transaction<rev>(
            enriched_txn, header.base_fee_per_gas, chain.get_chain_id()));

        // rodb is not thread safe
        thread_local mpt::Db db{
            mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = dbname_paths}};
        thread_local TrieDb ro{db};

        ro.set_block_number(block_number);
        BlockState block_state{ro};
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
    std::vector<uint8_t> const &rlp_txn, std::vector<uint8_t> const &rlp_header,
    std::vector<uint8_t> const &rlp_sender, uint64_t const block_number,
    std::string const &triedb_path, std::string const &blockdb_path,
    monad_state_override_set const &state_overrides)
{
    byte_string_view rlp_txn_view(rlp_txn.begin(), rlp_txn.end());
    auto const txn_result = rlp::decode_transaction(rlp_txn_view);
    MONAD_ASSERT(!txn_result.has_error());
    MONAD_ASSERT(rlp_txn_view.empty());
    auto const txn = txn_result.value();

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

    BlockHashBufferFinalized buffer{};
    for (size_t i = block_number < 256 ? 1 : block_number - 255;
         i <= block_number;
         ++i) {
        auto const path =
            std::filesystem::path{blockdb_path} / std::to_string(i);
        MONAD_ASSERT(std::filesystem::exists(path));
        std::ifstream istream(path);
        std::ostringstream buf;
        buf << istream.rdbuf();
        auto view = byte_string_view{
            (unsigned char *)buf.view().data(), buf.view().size()};
        auto const block_result = rlp::decode_block(view);
        MONAD_ASSERT(block_result.has_value());
        MONAD_ASSERT(view.empty());
        auto const &block = block_result.assume_value();
        buffer.set(i - 1, block.header.parent_hash);
    }

    std::vector<std::filesystem::path> paths;
    if (std::filesystem::is_block_file(triedb_path)) {
        paths.emplace_back(triedb_path);
    }
    else {
        MONAD_ASSERT(std::filesystem::is_directory(triedb_path));
        for (auto const &file :
             std::filesystem::directory_iterator(triedb_path)) {
            paths.emplace_back(file.path());
        }
    }
    auto const result = eth_call_impl(
        txn,
        block_header,
        block_number,
        sender,
        buffer,
        paths,
        state_overrides);
    monad_evmc_result ret;
    if (MONAD_UNLIKELY(result.has_error())) {
        ret.status_code = INT_MAX;
        ret.message = result.error().message().c_str();
    }
    else {
        int64_t const gas_used = static_cast<int64_t>(txn.gas_limit) -
                                 result.assume_value().gas_left;
        ret.status_code = result.assume_value().status_code;
        ret.output_data = {
            result.assume_value().output_data,
            result.assume_value().output_data +
                result.assume_value().output_size};
        ret.gas_used = gas_used;
        ret.gas_refund = result.assume_value().gas_refund;
    }
    return ret;
}
