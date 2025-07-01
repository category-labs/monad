#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/likely.h>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/precompiles.hpp>
#include <monad/execution/trace/prestate_tracer.hpp>
#include <monad/state3/account_state.hpp>
#include <monad/state3/state.hpp>

#include <nlohmann/json.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

using json = nlohmann::json;

// Optimized bytes_to_hex: manual nibble conversion without fmt overhead
static constexpr char hex_chars[] = "0123456789abcdef";

template <std::size_t N>
std::string bytes_to_hex(uint8_t const (&input)[N])
{
    // Reserve exactly 2*N + 2 chars
    std::string out;
    out.resize(2 * N + 2);
    out[0] = '0';
    out[1] = 'x';
    for (std::size_t i = 0; i < N; ++i) {
        uint8_t byte = input[i];
        out[2 + 2 * i] = hex_chars[(byte >> 4) & 0xF];
        out[2 + 2 * i + 1] = hex_chars[byte & 0xF];
    }
    return out;
}

std::string byte_string_to_hex(byte_string_view view)
{
    auto const N = view.length();
    // Reserve exactly 2*N + 2 chars
    std::string out;
    out.resize(2 * N + 2);
    out[0] = '0';
    out[1] = 'x';
    for (std::size_t i = 0; i < N; ++i) {
        uint8_t byte = view[i];
        out[2 + 2 * i] = hex_chars[(byte >> 4) & 0xF];
        out[2 + 2 * i + 1] = hex_chars[byte & 0xF];
    }
    return out;
}

StorageDeltas generate_storage_deltas(
    PrestateTracerBase::Map<bytes32_t, bytes32_t> const &original,
    PrestateTracerBase::Map<bytes32_t, bytes32_t> const &current)
{
    StorageDeltas deltas{};
    for (auto const &[key, value] : original) {
        if (auto const it = current.find(key); it != current.end()) {
            deltas.emplace(key, std::make_pair(value, it->second));
        }
        else {
            deltas.emplace(key, std::make_pair(value, bytes32_t{}));
        }
    }
    return deltas;
}

json storage_to_json(
    PrestateTracerBase::Map<bytes32_t, bytes32_t> const &storage)
{
    json res = json::object();
    for (auto const &[key, value] : storage) {
        auto const key_json = bytes_to_hex(key.bytes);
        auto const value_json = bytes_to_hex(value.bytes);
        res[key_json] = value_json;
    }
    return res;
}

json account_to_json(std::optional<Account> const &account, State &state)
{
    json res = json::object();
    if (MONAD_UNLIKELY(!account.has_value())) {
        // If account is created, then only show 'balance = "0x0"'
        res["balance"] = "0x0";
    }
    else {
        // Otherwise manually copy all the fields
        auto const &balance = account.value().balance;
        auto const &code_hash = account.value().code_hash;
        auto const nonce = account.value().nonce;

        res["balance"] = "0x" + intx::to_string(balance, 16);
        if (code_hash != NULL_HASH) {
            auto const icode = state.read_code(code_hash)->intercode();
            res["code"] = byte_string_to_hex(
                byte_string_view(icode->code(), icode->code_size()));
        }
        if (nonce != 0) {
            res["nonce"] = nonce; // nonce is kept in integer format
        }
    }
    return res;
}

json account_state_to_json(AccountState const &as, State &state)
{
    auto const &account = as.account_;
    auto const &storage = as.storage_;

    json res = account_to_json(account, state);
    if (!storage.empty() && account.has_value()) {
        res["storage"] = storage_to_json(storage);
    }
    return res;
}

PreState &&NoopPrestateTracer::get_pre_state()
{
    return std::move(null_pre_state_);
}

StateDeltas &&NoopPrestateTracer::get_state_deltas()
{
    return std::move(null_state_deltas_);
}

PrestateTracer::PrestateTracer(State const &state)
{
    auto original_account_states = state.get_original_accounts();
    auto current_account_states = state.get_current_accounts();

    pre_state_ = original_account_states;

    for (auto &[address, original_account_state] : original_account_states) {
        if (auto it = current_account_states.find(address);
            it != current_account_states.end()) {
            // Setters are called
            auto &current_account_state = it->second;
            auto &current_account = current_account_state.account_;
            auto &current_storage = current_account_state.storage_;
            auto &original_account = original_account_state.account_;
            auto &original_storage = original_account_state.storage_;
            if (MONAD_UNLIKELY(!current_account.has_value())) {
                // current account is destructed
                if (MONAD_UNLIKELY(!original_account.has_value())) {
                    // both original and current = NULL => no delta
                    continue;
                }
                else {
                    StateDelta state_delta{
                        .account = {original_account, std::nullopt},
                        .storage =
                            generate_storage_deltas(original_storage, {}),
                    };
                    state_deltas_.emplace(address, std::move(state_delta));
                }
            }
            else if (MONAD_UNLIKELY(!original_account.has_value())) {
                StateDelta state_delta{
                    .account = {std::nullopt, current_account},
                    .storage = generate_storage_deltas({}, current_storage),
                };
                state_deltas_.emplace(address, std::move(state_delta));
            }
            else {
                // remove unchanged storage values
                for (auto it = original_storage.begin();
                     it != original_storage.end();) {
                    auto it1 = current_storage.find(it->first);
                    if (it1 == current_storage.end()) {
                        it = original_storage.erase(it);
                    }
                    else {
                        if (it->second == it1->second) {
                            current_storage.erase(it1);
                            it = original_storage.erase(it);
                        }
                        else {
                            ++it;
                        }
                    }
                }

                if (!(original_account == current_account &&
                      original_storage == current_storage)) {
                    StateDelta state_delta{
                        .account = {original_account, current_account},
                        .storage = generate_storage_deltas(
                            original_storage, current_storage),
                    };
                    state_deltas_.emplace(address, std::move(state_delta));
                }
            }
        }
    }
}

PreState &&PrestateTracer::get_pre_state()
{
    return std::move(pre_state_);
}

StateDeltas &&PrestateTracer::get_state_deltas()
{
    return std::move(state_deltas_);
}

json state_to_json(PreState const &pre_state, State &state)
{
    json res = json::object();
    for (auto const &[address, as] : pre_state) {
        // TODO: Because this address is "touched". Should we keep this for
        // monad?
        if (MONAD_UNLIKELY(address == ripemd_address)) {
            continue;
        }
        auto const key = bytes_to_hex(address.bytes);
        res[key] = account_state_to_json(as, state);
    }
    return res;
}

json state_deltas_to_json(StateDeltas const &state_deltas, State &state)
{
    json pre = json::object();
    json post = json::object();
    for (auto const &[address, state_delta] : state_deltas) {
        auto const address_key = bytes_to_hex(address.bytes);
        // Account
        {
            auto const &original_account = state_delta.account.first;
            auto const &current_account = state_delta.account.second;

            // The accounts in the pre object will still contain all of their
            // basic fields—nonce, balance, and code—even if those fields have
            // not been modified
            pre[address_key] = account_to_json(original_account, state);
            // The post object is more selective - it only contains the specific
            // fields that were actually modified during the transaction
            if (!(original_account.has_value() &&
                  current_account.has_value())) {
                post[address_key] = account_to_json(current_account, state);
            }
            else {
                if (original_account->balance != current_account->balance) {
                    post[address_key]["balance"] =
                        "0x" + intx::to_string(current_account->balance, 16);
                }
                if (original_account->code_hash != current_account->code_hash) {
                    post[address_key]["code_hash"] =
                        bytes_to_hex(current_account->code_hash.bytes);
                }
                if (original_account->nonce != current_account->nonce) {
                    post[address_key]["nonce"] = current_account->nonce;
                }
            }
        }
        // Storage
        {
            json pre_storage = json::object();
            json post_storage = json::object();
            for (auto const &[key, storage_delta] : state_delta.storage) {
                auto const key_json = bytes_to_hex(key.bytes);
                auto const &original_storage = storage_delta.first;
                auto const &current_storage = storage_delta.second;
                if (MONAD_LIKELY(original_storage != bytes32_t{})) {
                    pre_storage[key_json] =
                        bytes_to_hex(original_storage.bytes);
                }
                if (MONAD_LIKELY(current_storage != bytes32_t{})) {
                    post_storage[key_json] =
                        bytes_to_hex(current_storage.bytes);
                }
            }
            if (!pre_storage.empty()) {
                pre[address_key]["storage"] = std::move(pre_storage);
            }
            if (!post_storage.empty()) {
                post[address_key]["storage"] = std::move(post_storage);
            }
        }
    }
    json res = json::object();
    res["pre"] = std::move(pre);
    res["post"] = std::move(post);
    return res;
}

json state_to_json_with_tx_hash(
    PreState const &pre_state, Transaction const &tx, State &state)
{
    json res = json::object();
    auto const hash = keccak256(rlp::encode_transaction(tx));
    auto const key = bytes_to_hex(hash.bytes);
    res[key] = state_to_json(pre_state, state);
    return res;
}

json state_deltas_to_json_with_tx_hash(
    StateDeltas const &state_deltas, Transaction const &tx, State &state)
{
    json res = json::object();
    auto const hash = keccak256(rlp::encode_transaction(tx));
    auto const key = bytes_to_hex(hash.bytes);
    res[key] = state_deltas_to_json(state_deltas, state);
    return res;
}

MONAD_NAMESPACE_END
