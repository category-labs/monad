#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/likely.h>
#include <monad/core/rlp/account_rlp.hpp>
#include <monad/db/db.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/fmt/state_deltas_fmt.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/state3/state.hpp>

#include <quill/detail/LogMacros.h>

#include <cstdint>
#include <fstream>
#include <optional>
#include <string>

namespace
{
    static std::ofstream output_account("account.csv");
    static std::ofstream output_storage("storage.csv");
};

MONAD_NAMESPACE_BEGIN

BlockState::BlockState(Db &db)
    : db_{db}
    , state_{}
    , code_{}
{
}

std::optional<Account> BlockState::read_account(Address const &address)
{
    // block state
    {
        StateDeltas::const_accessor it{};
        if (MONAD_LIKELY(state_.find(it, address))) {
            return it->second.account.second;
        }
    }
    // database
    {
        auto const result = db_.read_account(address);
        StateDeltas::const_accessor it{};
        state_.emplace(
            it,
            address,
            StateDelta{.account = {result, result}, .storage = {}});
        return it->second.account.second;
    }
}

bytes32_t BlockState::read_storage(
    Address const &address, uint64_t const incarnation, bytes32_t const &key)
{
    // block state
    {
        StateDeltas::const_accessor it{};
        MONAD_ASSERT(state_.find(it, address));
        auto const &storage = it->second.storage;
        {
            StorageDeltas::const_accessor it2{};
            if (MONAD_LIKELY(storage.find(it2, key))) {
                return it2->second.second;
            }
        }
    }
    // database
    {
        auto const result =
            incarnation == 0 ? db_.read_storage(address, key) : bytes32_t{};
        StateDeltas::accessor it{};
        MONAD_ASSERT(state_.find(it, address));
        auto &storage = it->second.storage;
        {
            StorageDeltas::const_accessor it2{};
            storage.emplace(it2, key, std::make_pair(result, result));
            return it2->second.second;
        }
    }
}

std::shared_ptr<CodeAnalysis> BlockState::read_code(bytes32_t const &code_hash)
{
    // block state
    {
        Code::const_accessor it{};
        if (MONAD_LIKELY(code_.find(it, code_hash))) {
            return it->second;
        }
    }
    // database
    {
        auto const result = db_.read_code(code_hash);
        MONAD_ASSERT(result);
        MONAD_ASSERT(
            code_hash == NULL_HASH || !result->executable_code.empty());
        Code::const_accessor it{};
        code_.emplace(it, code_hash, result);
        return it->second;
    }
}

bool BlockState::can_merge(State const &state)
{
    for (auto const &[address, account_state] : state.original_) {
        auto const &account = account_state.account_;
        auto const &storage = account_state.storage_;
        StateDeltas::const_accessor it{};
        MONAD_ASSERT(state_.find(it, address));
        if (account != it->second.account.second) {
            return false;
        }
        // TODO account.has_value()???
        for (auto const &[key, value] : storage) {
            StorageDeltas::const_accessor it2{};
            MONAD_ASSERT(it->second.storage.find(it2, key));
            if (value != it2->second.second) {
                return false;
            }
        }
    }
    return true;
}

void BlockState::merge(
    State const &state, std::optional<block_num_t> const block_number,
    std::optional<uint64_t> const txn_number,
    std::optional<Address> const sender,
    std::optional<Address> const beneficiary)
{
    ankerl::unordered_dense::segmented_set<bytes32_t> code_hashes;

    for (auto const &[address, stack] : state.state_) {
        MONAD_ASSERT(stack.size() == 1);
        MONAD_ASSERT(stack.version() == 0);
        auto const &account_state = stack.recent();
        auto const &account = account_state.account_;
        if (account.has_value()) {
            code_hashes.insert(account.value().code_hash);
        }
    }

    for (auto const &code_hash : code_hashes) {
        auto const it = state.code_.find(code_hash);
        if (it == state.code_.end()) {
            continue;
        }
        code_.emplace(code_hash, it->second); // TODO try_emplace
    }

    for (auto const &[address, stack] : state.state_) {
        auto const &account_state = stack.recent();
        auto const &account = account_state.account_;
        auto const &storage = account_state.storage_;
        StateDeltas::accessor it{};
        MONAD_ASSERT(state_.find(it, address));
        it->second.account.second = account;

        // logging code
        auto const &account_original = it->second.account.first;
        auto const address_string = fmt::format(
            "0x{:02x}", fmt::join(std::as_bytes(std::span(address.bytes)), ""));

        auto const is_sender =
            sender.has_value() && (sender.value() == address);
        auto const is_beneficiary =
            beneficiary.has_value() && (beneficiary.value() == address);

        auto const account_rlp_original =
            account_original.has_value()
                ? rlp::encode_account(account_original.value())
                : byte_string{};
        auto const account_string_original = fmt::format(
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(account_rlp_original)), ""));
        auto const account_rlp_current =
            account.has_value() ? rlp::encode_account(account.value())
                                : byte_string{};
        auto const account_string_current = fmt::format(
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(account_rlp_current)), ""));
        if (block_number.has_value()) {
            output_account << block_number.value() << ", " << txn_number.value()
                           << ", " << address_string << ", "
                           << account_string_original << ", "
                           << account_string_current << ", " << is_sender
                           << ", " << is_beneficiary << std::endl;
        }

        if (account.has_value()) {
            for (auto const &[key, value] : storage) {
                StorageDeltas::accessor it2{};
                MONAD_ASSERT(it->second.storage.find(it2, key));
                it2->second.second = value;

                // logging code
                auto const storage_key_string = fmt::format(
                    "0x{:02x}",
                    fmt::join(std::as_bytes(std::span(it2->first.bytes)), ""));
                auto const storage_value_string_original = fmt::format(
                    "0x{:02x}",
                    fmt::join(
                        std::as_bytes(std::span(it2->second.first.bytes)), ""));
                auto const storage_value_string_current = fmt::format(
                    "0x{:02x}",
                    fmt::join(
                        std::as_bytes(std::span(it2->second.second.bytes)),
                        ""));

                if (block_number.has_value()) {
                    output_storage
                        << block_number.value() << ", " << txn_number.value()
                        << ", " << address_string << ", " << storage_key_string
                        << ", " << storage_value_string_original << ", "
                        << storage_value_string_current << std::endl;
                }

                // end of logging code
            }
        }
        else {
            it->second.storage.clear();
        }
    }
}

void BlockState::commit()
{
    db_.commit(state_, code_);
}

void BlockState::log_debug()
{
    LOG_DEBUG("State Deltas: {}", state_);
    LOG_DEBUG("Code Deltas: {}", code_);
}

MONAD_NAMESPACE_END
