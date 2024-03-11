#include <monad/core/assert.h>
#include <monad/core/rlp/account_rlp.hpp>
#include <monad/db/config.hpp>
#include <monad/db/read_only_trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/rlp/encode2.hpp>

#include <ethash/keccak.hpp>

#include <algorithm>
#include <chrono>
#include <cstdlib>

MONAD_DB_NAMESPACE_BEGIN

using namespace monad::mpt;

std::optional<Account> ReadOnlyTrieDb::read_account(Address const &addr)
{
    auto const value = ro_db_.get(
        concat(state_nibble, NibblesView{to_key(addr)}), curr_block_id_);
    if (!value.has_value()) {
        return std::nullopt;
    }

    auto encoded_account = value.value();
    auto acct = rlp::decode_account(encoded_account);
    MONAD_DEBUG_ASSERT(!acct.has_error());
    MONAD_DEBUG_ASSERT(encoded_account.empty());
    acct.value().incarnation = 0;
    return acct.value();
}

bytes32_t
ReadOnlyTrieDb::read_storage(Address const &addr, bytes32_t const &key)
{
    auto const value = ro_db_.get(
        concat(
            state_nibble, NibblesView{to_key(addr)}, NibblesView{to_key(key)}),
        curr_block_id_);
    if (!value.has_value()) {
        return {};
    }
    MONAD_ASSERT(value.value().size() <= sizeof(bytes32_t));
    bytes32_t ret;
    std::copy_n(
        value.value().begin(),
        value.value().size(),
        ret.bytes + sizeof(bytes32_t) - value.value().size());
    return ret;
};

std::shared_ptr<CodeAnalysis>
ReadOnlyTrieDb::read_code(bytes32_t const &code_hash)
{
    // TODO read code analysis object
    auto const value = ro_db_.get(
        concat(code_nibble, NibblesView{to_byte_string_view(code_hash.bytes)}),
        curr_block_id_);
    if (!value.has_value()) {
        return std::make_shared<CodeAnalysis>(analyze({}));
    }
    return std::make_shared<CodeAnalysis>(analyze(value.assume_value()));
}

bytes32_t ReadOnlyTrieDb::state_root()
{
    auto const value = ro_db_.get_data(state_nibbles, curr_block_id_);
    if (!value.has_value() || value.value().empty()) {
        return NULL_ROOT;
    }
    bytes32_t root;
    MONAD_ASSERT(value.value().size() == sizeof(bytes32_t));
    std::copy_n(value.value().data(), sizeof(bytes32_t), root.bytes);
    return root;
}

uint64_t ReadOnlyTrieDb::current_block_number() const
{
    return curr_block_id_;
}

MONAD_DB_NAMESPACE_END
