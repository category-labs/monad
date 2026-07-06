// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/assert.h>
#include <category/core/basic_formatter.hpp> // NOLINT
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/cli/help_formatter.hpp>
#include <category/core/config.hpp>
#include <category/core/hex.hpp>
#include <category/core/keccak.h>
#include <category/core/keccak.hpp>
#include <category/core/log.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/fmt/account_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/fmt/receipt_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/log_level_map.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/receipt_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/db/db_snapshot.h>
#include <category/execution/ethereum/db/db_snapshot_filesystem.h>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/nibbles_view_fmt.hpp> // NOLINT
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/util.hpp>

#include <CLI/CLI.hpp>
#include <evmc/evmc.hpp>
#include <intx/intx.hpp>
#include <nlohmann/json.hpp>
#include <quill/bundled/fmt/format.h>

#include <quill/std/Chrono.h>
#include <quill/std/FilesystemPath.h>
#include <quill/std/Vector.h>

#include <algorithm>
#include <cctype>
#include <cerrno>
#include <charconv>
#include <chrono>
#include <cmath>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <ranges>
#include <span>
#include <spanstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <tuple>
#include <type_traits>
#include <unordered_map>
#include <utility>
#include <vector>

#include <stdio.h>
#include <sys/resource.h>
#include <unistd.h>

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

////////////////////////////////////////
// CLI input parsing helpers
////////////////////////////////////////

bool is_numeric(std::string_view const str)
{
    return !str.empty() && std::all_of(str.begin(), str.end(), ::isdigit);
}

std::vector<std::string>
tokenize(std::string_view const input, char const delim = ' ')
{
    std::ispanstream iss(input);
    std::vector<std::string> tokens;
    std::string token;
    while (std::getline(iss, token, delim)) {
        if (!token.empty()) {
            tokens.emplace_back(std::move(token));
        }
    }
    return tokens;
}

////////////////////////////////////////
// TrieDb Helpers
////////////////////////////////////////

std::string_view table_as_string(unsigned char const table_id)
{
    switch (table_id) {
    case STATE_NIBBLE:
        return "state";
    case CODE_NIBBLE:
        return "code";
    case RECEIPT_NIBBLE:
        return "receipt";
    case TRANSACTION_NIBBLE:
        return "transaction";
    case DOMAIN_RECEIPT_NIBBLE:
        return "domain_receipt";
    case DOMAIN_TRANSACTION_NIBBLE:
        return "domain_transaction";
    case DOMAIN_TX_HASH_NIBBLE:
        return "domain_transaction_hash";
    default:
        return "invalid";
    }
}

template <class T>
    requires std::same_as<T, byte_string_view> ||
             std::same_as<T, std::string_view>
auto to_triedb_key(T input, bool already_hashed = false)
{
    using res = std::invoke_result_t<hash256 (*)(T), T>;
    return already_hashed ? byte_string{input.data(), input.size()}
                          : byte_string{keccak256(input).bytes, sizeof(res)};
}

void print_account(Account const &acct)
{
    fmt::print("{}\n\n", acct);
}

void print_receipt(Receipt const &receipt)
{
    fmt::print("{}\n\n", receipt);
}

void print_transaction(Transaction const &tx, Address const sender)
{
    auto const encoded = rlp::encode_transaction(tx);
    fmt::print("{}\n", tx);
    fmt::print("Sender={}\n", sender);
    fmt::print(
        "Encoded=0x{:02x}\n\n",
        fmt::join(std::as_bytes(std::span(encoded)), ""));
}

void print_storage(bytes32_t const key, bytes32_t const val)
{
    fmt::print("Storage{{key={},value={}}}\n\n", key, val);
}

void print_code(byte_string_view const code)
{
    fmt::print(
        "{}\n\n",
        (code.empty()
             ? "EMPTY"
             : fmt::format(
                   "0x{:02x}", fmt::join(std::as_bytes(std::span(code)), ""))));
}

struct DbStateMachine
{
    Db &db;

    uint64_t curr_version{INVALID_BLOCK_NUM};
    bytes32_t curr_block_id{}; // empty means finalized
    Nibbles curr_section_prefix{};
    unsigned char curr_table_id{INVALID_NIBBLE};

    enum class DbState
    {
        unset = 0,
        version_number,
        proposal_or_finalize,
        table,
        invalid
    } state{DbState::unset};

    explicit DbStateMachine(Db &db)
        : db(db)
    {
    }

    void set_version(uint64_t const version)
    {
        MONAD_ASSERT(version != INVALID_BLOCK_NUM);
        if (state != DbState::unset) {
            fmt::println(
                "Error: already at version {}, use 'back' to move cursor "
                "up and try again",
                curr_version);
            return;
        }
        MONAD_ASSERT(curr_version == INVALID_BLOCK_NUM);
        MONAD_ASSERT(curr_section_prefix.nibble_size() == 0);

        auto const min_version = db.get_earliest_version();
        auto const max_version = db.get_latest_version();
        if (min_version > version || max_version < version) {
            fmt::println(
                "Error: invalid version {}. Please choose a version in range "
                "[{}, {}]",
                version,
                min_version,
                max_version);
            return;
        }

        curr_version = version;
        state = DbState::version_number;

        fmt::println("Success! Set version to {}\n", curr_version);
        if (list_finalized_and_proposals(version)) {
            fmt::println("Type \"proposal [block_id]\" or "
                         "\"finalized\" to set section");
        }
        else {
            fmt::println(
                "WARNING: version {} has no proposals or finalized section",
                curr_version);
        }
    }

    // Returns `true` if at least one finalized or proposal section exists,
    // otherwise `false`.
    bool list_finalized_and_proposals(uint64_t const version)
    {
        if (version == INVALID_BLOCK_NUM) {
            fmt::println("Error: invalid version to list sections, set to a "
                         "valid version and try again");
            return false;
        }
        auto const finalized_res = db.find(finalized_nibbles, version);
        auto const block_ids = get_proposal_block_ids(db, version);
        if (finalized_res.has_error() && block_ids.empty()) {
            return false;
        }
        fmt::println("List sections of version {}: ", version);
        if (finalized_res.has_value()) {
            fmt::println("    finalized : yes ", version);
        }
        else {
            fmt::println("    finalized : no ", version);
        }
        fmt::println("    proposals : {}\n", block_ids);
        return true;
    }

    void set_proposal_or_finalized(bytes32_t const &block_id)
    {
        if (state != DbState::version_number) {
            fmt::println("Error: at wrong part of trie, only allow set section "
                         "when cursor is set to a version.");
            return;
        }
        MONAD_ASSERT(curr_section_prefix.nibble_size() == 0);
        curr_block_id = block_id;
        if (block_id != bytes32_t{}) { // set proposal
            auto const prefix = proposal_prefix(block_id);
            if (db.find(prefix, curr_version).has_value()) {
                curr_section_prefix = prefix;
                state = DbState::proposal_or_finalize;
                fmt::println(
                    "Success! Set to proposal block_id {} of version {}",
                    block_id,
                    curr_version);
            }
            else {
                fmt::println(
                    "Could not locate proposal of block_id {}", block_id);
            }
        }
        else {
            if (db.find(finalized_nibbles, curr_version).has_value()) {
                curr_section_prefix = finalized_nibbles;
                state = DbState::proposal_or_finalize;
                fmt::println(
                    "Success! Set to finalized of version {}", curr_version);
            }
            else {
                fmt::println(
                    "Version {} does not contain finalized section",
                    curr_version);
            }
        }
    }

    void set_table(unsigned char const table_id)
    {
        if (state != DbState::proposal_or_finalize) {
            fmt::println("Error: at wrong part of trie, only allow set table "
                         "when cursor is set to a specific version number.");
            return;
        }
        MONAD_ASSERT(curr_section_prefix.nibble_size() > 0);

        if (table_id == STATE_NIBBLE || table_id == CODE_NIBBLE ||
            table_id == RECEIPT_NIBBLE || table_id == TRANSACTION_NIBBLE ||
            table_id == DOMAIN_RECEIPT_NIBBLE ||
            table_id == DOMAIN_TRANSACTION_NIBBLE ||
            table_id == DOMAIN_TX_HASH_NIBBLE) {
            fmt::println(
                "Setting cursor to version {}, table {} ...",
                curr_version,
                table_as_string(table_id));
            auto const res =
                db.find(concat(curr_section_prefix, table_id), curr_version);
            if (res.has_value()) {
                NodeCursor const cursor = res.assume_value();
                state = DbState::table;
                curr_table_id = table_id;
                if (curr_table_id != CODE_NIBBLE) {
                    bytes32_t merkle_root = cursor.node->data().empty()
                                                ? NULL_ROOT
                                                : to_bytes(cursor.node->data());
                    fmt::println(" * Merkle root is {}", merkle_root);
                }
                fmt::println(" * \"node_stats\" will display a summary of node "
                             "metadata");
                fmt::println(" * Next, try look up a key in this table using "
                             "\"get [key]\"");
            }
            else {
                fmt::println(
                    "Couldn't find root node for {} -- {}",
                    table_as_string(table_id),
                    res.error().message().c_str());
                if (table_id == DOMAIN_RECEIPT_NIBBLE ||
                    table_id == DOMAIN_TRANSACTION_NIBBLE ||
                    table_id == DOMAIN_TX_HASH_NIBBLE) {
                    // Domain tables can legitimately have no root at the
                    // selected version. Keep the table selected so `get` can
                    // report an ordinary miss instead of a cursor error.
                    state = DbState::table;
                    curr_table_id = table_id;
                }
            }
        }
        else {
            fmt::println("Invalid table id");
        }
    }

    void print_domain_root(uint64_t const domain_id) const
    {
        if (state != DbState::table ||
            (curr_table_id != DOMAIN_RECEIPT_NIBBLE &&
             curr_table_id != DOMAIN_TRANSACTION_NIBBLE)) {
            fmt::println("Select a domain receipt or transaction table first.");
            return;
        }
        uint8_t bytes[sizeof(domain_id)];
        intx::be::store(bytes, domain_id);
        auto const result = db.find(
            concat(
                curr_section_prefix,
                curr_table_id,
                NibblesView{to_byte_string_view(bytes)}),
            curr_version);
        if (!result) {
            fmt::println("Could not find domain {}", domain_id);
            return;
        }
        auto const &node = result.assume_value().node;
        bytes32_t const root =
            node->data().empty() ? NULL_ROOT : to_bytes(node->data());
        fmt::println("Domain {} Merkle root is {}", domain_id, root);
    }

    Result<NodeCursor> lookup(NibblesView const key) const
    {
        if (state != DbState::table) {
            fmt::println("Error: at wrong part of trie, please navigate cursor "
                         "to a table before lookup.");
        }
        MONAD_ASSERT(!curr_section_prefix.empty());
        MONAD_ASSERT(curr_table_id != INVALID_NIBBLE);
        fmt::println(
            "Looking up key {} \nat version {} on table {} ... ",
            key,
            curr_version,
            table_as_string(curr_table_id));
        return db.find(
            concat(curr_section_prefix, curr_table_id, key), curr_version);
    }

    bool has_domain_block(uint64_t const domain_id) const
    {
        uint8_t domain_bytes[sizeof(domain_id)];
        intx::be::store(domain_bytes, domain_id);
        auto const result = db.find(
            concat(
                curr_section_prefix,
                DOMAIN_BLOCK_HEADER_NIBBLE,
                NibblesView{to_byte_string_view(domain_bytes)}),
            curr_version);
        if (!result.has_value()) {
            return false;
        }
        auto encoded = result.value().node->value();
        auto const header = rlp::decode_block_header(encoded);
        return header.has_value() && header.value().number == curr_version;
    }

    void back()
    {
        switch (state) {
        case DbState::table:
            state = DbState::proposal_or_finalize;
            if (curr_block_id != bytes32_t{}) {
                fmt::println(
                    "At proposal block_id {} of version {}",
                    curr_block_id,
                    curr_version);
            }
            else {
                fmt::println(
                    "At finalized section of version {}", curr_version);
            }
            break;
        case DbState::proposal_or_finalize:
            state = DbState::version_number;
            curr_section_prefix = {};
            curr_block_id = bytes32_t{};
            fmt::println(
                "At version {}. Type \"proposal [block_id]\" or "
                "\"finalized\" to set section",
                curr_version);
            break;
        case DbState::version_number:
            curr_version = INVALID_BLOCK_NUM;
            state = DbState::unset;
            fmt::println("Version is unset");
            break;
        default:
            curr_version = INVALID_BLOCK_NUM;
        }
        curr_table_id = INVALID_NIBBLE;
    }
};

////////////////////////////////////////
// Full-state dump — TraverseMachines that walk the root state table and the
// domain state table. Domain state lives under
// DOMAIN_STATE_NIBBLE + be64(domain_id), not in synthetic root accounts.
//
// Root state trie layout, relative to STATE_NIBBLE:
//   64  nibbles — account leaf (key = keccak(address))
//   128 nibbles — account storage slot (key = keccak(slot))
//
// Domain state trie layout, relative to DOMAIN_STATE_NIBBLE:
//   16  nibbles — domain id (be64)
//   80  nibbles — domain-local account leaf
//   144 nibbles — domain-local account storage slot
////////////////////////////////////////

struct AccountInfo
{
    Account account;
    std::map<bytes32_t, bytes32_t> storage;
};

using AccountDump = std::map<Address, AccountInfo>;

void add_storage_leaf_to_dump(
    AccountInfo &account_info, byte_string_view enc, bool const page_encoded)
{
    if (!page_encoded) {
        auto res = decode_storage_db(enc);
        if (res.has_value()) {
            auto const &[slot, value] = res.value();
            account_info.storage[slot] = value;
        }
        return;
    }

    auto raw_res = decode_storage_db_raw(enc);
    if (!raw_res.has_value() || !enc.empty()) {
        return;
    }
    bytes32_t const page_key = to_bytes(raw_res.value().first);
    auto const page = decode_storage_page(raw_res.value().second);
    if (!page.has_value()) {
        return;
    }
    for (uint8_t off = 0; off < storage_page_t::SLOTS; ++off) {
        auto const &slot_value = page.value()[off];
        if (slot_value == bytes32_t{}) {
            continue;
        }
        account_info.storage[compute_slot_key(page_key, off)] = slot_value;
    }
}

class AccountTrieDumpMachine final : public TraverseMachine
{
public:
    AccountDump accounts;

private:
    Nibbles path_;
    uint16_t const account_depth_;
    uint16_t const storage_depth_;
    bool const page_encoded_;
    std::optional<Address> current_addr_;

public:
    AccountTrieDumpMachine(
        uint16_t const account_depth = sizeof(bytes32_t) * 2,
        uint16_t const storage_depth = sizeof(bytes32_t) * 4,
        bool const page_encoded = false)
        : account_depth_{account_depth}
        , storage_depth_{storage_depth}
        , page_encoded_{page_encoded}
    {
    }

    virtual bool down(unsigned char const branch, Node const &node) override
    {
        if (branch != INVALID_BRANCH) {
            path_ = concat(NibblesView{path_}, branch, node.path_nibble_view());
        }

        if (node.has_value()) {
            auto const nibble_size = path_.nibble_size();
            byte_string_view enc = node.value();

            if (nibble_size == account_depth_) {
                auto res = decode_account_db(enc);
                if (res.has_value()) {
                    auto const &[addr, acct] = res.value();
                    accounts[addr].account = acct;
                    current_addr_ = addr;
                }
            }
            else if (
                nibble_size == storage_depth_ && current_addr_.has_value()) {
                add_storage_leaf_to_dump(
                    accounts[*current_addr_], enc, page_encoded_);
            }
        }
        return true;
    }

    virtual void up(unsigned char const branch, Node const &node) override
    {
        if (branch == INVALID_BRANCH) {
            path_ = Nibbles{};
            return;
        }
        auto const path_view = NibblesView{path_};
        auto const nibbles_above =
            path_view.nibble_size() - node.path_nibbles_len() - 1;
        path_ = Nibbles{path_view.substr(0, nibbles_above)};

        if (path_.nibble_size() < account_depth_) {
            current_addr_ = std::nullopt;
        }
    }

    virtual std::unique_ptr<TraverseMachine> clone() const override
    {
        return std::make_unique<AccountTrieDumpMachine>(*this);
    }
};

struct DomainInfo
{
    bytes32_t state_root{NULL_ROOT};
    AccountDump accounts;
};

class DomainStateDumpMachine final : public TraverseMachine
{
public:
    std::map<uint64_t, DomainInfo> domains;

private:
    static constexpr uint16_t domain_depth_ = sizeof(uint64_t) * 2;
    static constexpr uint16_t account_depth_ =
        domain_depth_ + sizeof(bytes32_t) * 2;
    static constexpr uint16_t storage_depth_ =
        domain_depth_ + sizeof(bytes32_t) * 4;

    Nibbles path_;
    bool const page_encoded_;
    std::optional<uint64_t> current_domain_;
    std::optional<Address> current_addr_;

    static uint64_t domain_from_path(NibblesView const path)
    {
        MONAD_ASSERT(path.nibble_size() >= domain_depth_);
        return deserialize_from_big_endian<uint64_t>(
            path.substr(0, domain_depth_));
    }

public:
    explicit DomainStateDumpMachine(bool const page_encoded = false)
        : page_encoded_{page_encoded}
    {
    }

    virtual bool down(unsigned char const branch, Node const &node) override
    {
        if (branch != INVALID_BRANCH) {
            path_ = concat(NibblesView{path_}, branch, node.path_nibble_view());
        }

        if (node.has_value()) {
            auto const path_view = NibblesView{path_};
            auto const nibble_size = path_view.nibble_size();
            byte_string_view enc = node.value();

            if (nibble_size == account_depth_) {
                auto res = decode_account_db(enc);
                if (res.has_value()) {
                    uint64_t const domain = domain_from_path(path_view);
                    auto const &[addr, acct] = res.value();
                    domains[domain].accounts[addr].account = acct;
                    current_domain_ = domain;
                    current_addr_ = addr;
                }
            }
            else if (
                nibble_size == storage_depth_ && current_domain_.has_value() &&
                current_addr_.has_value()) {
                add_storage_leaf_to_dump(
                    domains[*current_domain_].accounts[*current_addr_],
                    enc,
                    page_encoded_);
            }
        }
        return true;
    }

    virtual void up(unsigned char const branch, Node const &node) override
    {
        if (branch == INVALID_BRANCH) {
            path_ = Nibbles{};
            return;
        }
        auto const path_view = NibblesView{path_};
        auto const nibbles_above =
            path_view.nibble_size() - node.path_nibbles_len() - 1;
        path_ = Nibbles{path_view.substr(0, nibbles_above)};

        auto const size = path_.nibble_size();
        if (size < account_depth_) {
            current_addr_ = std::nullopt;
        }
        if (size < domain_depth_) {
            current_domain_ = std::nullopt;
        }
    }

    virtual std::unique_ptr<TraverseMachine> clone() const override
    {
        return std::make_unique<DomainStateDumpMachine>(*this);
    }
};

nlohmann::json account_to_json(Account const &acct)
{
    nlohmann::json j;
    j["balance"] = acct.balance.to_string(10);
    j["nonce"] = acct.nonce;
    j["code_hash"] = "0x" + to_hex(acct.code_hash);
    return j;
}

nlohmann::json accounts_to_json(AccountDump const &accounts)
{
    auto accounts_json = nlohmann::json::object();
    for (auto const &[addr, info] : accounts) {
        auto a = account_to_json(info.account);
        if (!info.storage.empty()) {
            auto s = nlohmann::json::object();
            for (auto const &[slot, value] : info.storage) {
                s["0x" + to_hex(slot)] = "0x" + to_hex(value);
            }
            a["storage"] = s;
        }
        accounts_json["0x" + to_hex(addr)] = a;
    }
    return accounts_json;
}

std::string domain_key(uint64_t const domain)
{
    return "0x" + to_hex(serialize_as_big_endian<sizeof(domain)>(domain));
}

Nibbles finalized_domain_state_path(uint64_t const domain)
{
    auto const domain_bytes = serialize_as_big_endian<sizeof(domain)>(domain);
    return concat(
        FINALIZED_NIBBLE,
        DOMAIN_STATE_NIBBLE,
        NibblesView{byte_string_view{domain_bytes}});
}

bytes32_t
domain_state_root(Db &db, uint64_t const version, uint64_t const domain)
{
    auto res = db.find(finalized_domain_state_path(domain), version);
    if (!res.has_value() || res.value().node->data().empty()) {
        return NULL_ROOT;
    }
    auto const data = res.value().node->data();
    MONAD_ASSERT(data.size() == sizeof(bytes32_t));
    return to_bytes(data);
}

nlohmann::json build_state_dump_json(
    bytes32_t const &state_root, AccountTrieDumpMachine const &root_dump,
    DomainStateDumpMachine const &domain_dump, bool const page_encoded)
{
    nlohmann::json j;
    j["state_root"] = "0x" + to_hex(state_root);
    j["storage_encoding"] = page_encoded ? "page" : "slot";
    j["accounts"] = accounts_to_json(root_dump.accounts);

    auto &domains_json = j["domains"] = nlohmann::json::object();
    for (auto const &[domain, info] : domain_dump.domains) {
        nlohmann::json domain_json;
        domain_json["state_root"] = "0x" + to_hex(info.state_root);
        domain_json["accounts"] = accounts_to_json(info.accounts);
        domains_json[domain_key(domain)] = domain_json;
    }
    return j;
}

int dump_state_to_file(
    Db &db, uint64_t const version, std::filesystem::path const &out_path)
{
    bool const page_encoded =
        db.state_machine_type() == state_machine_kind::monad;
    auto const prefix = concat(FINALIZED_NIBBLE, STATE_NIBBLE);
    auto cursor_res = db.find(prefix, version);
    if (!cursor_res.has_value()) {
        LOG_ERROR(
            "could not find state table at version {} / finalized: {}",
            version,
            cursor_res.error().message().c_str());
        return 1;
    }
    NodeCursor const cursor = cursor_res.assume_value();
    bytes32_t const state_root =
        cursor.node->data().empty() ? NULL_ROOT : to_bytes(cursor.node->data());

    AccountTrieDumpMachine state_machine{
        sizeof(bytes32_t) * 2, sizeof(bytes32_t) * 4, page_encoded};
    bool const ok = db.traverse_blocking(cursor, state_machine, version);
    if (!ok) {
        LOG_ERROR("state traversal did not complete");
        return 1;
    }

    DomainStateDumpMachine domain_machine{page_encoded};
    auto const domain_prefix = concat(FINALIZED_NIBBLE, DOMAIN_STATE_NIBBLE);
    auto domain_cursor_res = db.find(domain_prefix, version);
    if (domain_cursor_res.has_value()) {
        bool const domain_ok = db.traverse_blocking(
            domain_cursor_res.assume_value(), domain_machine, version);
        if (!domain_ok) {
            LOG_ERROR("domain state traversal did not complete");
            return 1;
        }
        for (auto &[domain, info] : domain_machine.domains) {
            info.state_root = domain_state_root(db, version, domain);
        }
    }

    nlohmann::json const j = build_state_dump_json(
        state_root, state_machine, domain_machine, page_encoded);
    std::ofstream out(out_path);
    if (!out) {
        LOG_ERROR("could not open {} for writing", out_path.string());
        return 1;
    }
    out << j.dump(2) << '\n';
    out.close();
    LOG_INFO(
        "dumped {} root accounts and {} domains at version {} to {}",
        state_machine.accounts.size(),
        domain_machine.domains.size(),
        version,
        out_path.string());
    return 0;
}

////////////////////////////////////////
// Command actions
////////////////////////////////////////

void print_help()
{
    fmt::print(
        "List of commands:\n\n"
        "version [version_number]     -- Set the database version\n"
        "proposal [block_id] or finalized -- Set the section to query\n"
        "list sections                -- List any proposal or finalized "
        "section in current version\n"
        "table [state/receipt/transaction/code/domain_receipt/"
        "domain_transaction/domain_transaction_hash] -- Set the table "
        "to query\n"
        "domain_root [id]         -- Print selected domain table root\n"
        "get [key [extradata]]        -- Get the value for the given key\n"
        "node_stats                   -- Print node statistics for the given "
        "table\n"
        "back                         -- Move back to the previous level\n"
        "help                         -- Show this help message\n"
        "exit                         -- Exit the program\n"
        "\n"
        "For the `account` table. The user may optionally provide\n"
        "a storage slot as the second argument.\n");
}

void do_version(DbStateMachine &sm, std::string_view const version)
{
    uint64_t v{};
    auto [_, ec] =
        std::from_chars(version.data(), version.data() + version.size(), v);
    if (ec != std::errc()) {
        fmt::println("Invalid version: please input a number.");
    }
    else {
        sm.set_version(v);
    }
}

void do_proposal(DbStateMachine &sm, std::string_view const input)
{
    bytes32_t const block_id = evmc::literals::parse<bytes32_t>(input);
    if (block_id == bytes32_t{}) {
        fmt::println(
            "Invalid block_id input: please input a 32-byte hex string.");
    }
    else {
        sm.set_proposal_or_finalized(block_id);
    }
}

void do_table(DbStateMachine &sm, std::string_view const table_name)
{
    unsigned char table_nibble = INVALID_NIBBLE;
    if (table_name == "state") {
        table_nibble = STATE_NIBBLE;
    }
    else if (table_name == "receipt") {
        table_nibble = RECEIPT_NIBBLE;
    }
    else if (table_name == "transaction") {
        table_nibble = TRANSACTION_NIBBLE;
    }
    else if (table_name == "domain_receipt") {
        table_nibble = DOMAIN_RECEIPT_NIBBLE;
    }
    else if (table_name == "domain_transaction") {
        table_nibble = DOMAIN_TRANSACTION_NIBBLE;
    }
    else if (table_name == "domain_transaction_hash") {
        table_nibble = DOMAIN_TX_HASH_NIBBLE;
    }
    else if (table_name == "code") {
        table_nibble = CODE_NIBBLE;
    }

    if (table_nibble == INVALID_NIBBLE) {
        fmt::print("Invalid table provided!\n\n");
        print_help();
    }
    else {
        sm.set_table(table_nibble);
    }
}

void do_get_code(DbStateMachine const &sm, std::string_view const code_hash)
{
    auto const code_hex = from_hex(code_hash);
    if (!code_hex) {
        fmt::println("Code must be a valid hexadecimal value!");
        return;
    }
    auto const code_query_res = sm.lookup(NibblesView{code_hex.value()});
    if (!code_query_res) {
        fmt::println(
            "Could not find code {} -- {}",
            code_hash,
            code_query_res.error().message().c_str());
        return;
    }
    print_code(code_query_res.value().node->value());
}

void do_get_account(
    DbStateMachine const &sm, std::string_view const account,
    std::string_view const storage)
{
    auto const account_hex = from_hex(account);
    if (!account_hex) {
        fmt::println("Account must be a valid hexadecimal value!");
        return;
    }

    bool const account_is_hashed = (account_hex->size() == 32);
    auto const account_key =
        to_triedb_key(byte_string_view{account_hex.value()}, account_is_hashed);
    auto const account_query_res = sm.lookup(NibblesView{account_key});
    if (!account_query_res) {
        fmt::println(
            "Could not find account {} -- {}",
            account,
            account_query_res.error().message().c_str());
        return;
    }
    auto account_encoded = account_query_res.value().node->value();
    auto const acct_res = decode_account_db(account_encoded);
    if (!acct_res) {
        fmt::println(
            "Could not decode account data from TrieDb -- {}",
            acct_res.error().message().c_str());
        return;
    }
    print_account(acct_res.value().second);

    // Check if user provided a storage slot
    if (!storage.empty()) {
        bool storage_already_hashed = true;
        auto normalized_storage = std::string(storage);
        if (is_numeric(storage)) {
            size_t slot_id{};
            std::from_chars(
                storage.data(), storage.data() + storage.size(), slot_id);
            normalized_storage = std::format("{:064x}", slot_id);
            storage_already_hashed = false;
        }
        auto const storage_slot = from_hex(normalized_storage);
        if (!storage_slot) {
            fmt::println("Storage must be a valid hexadecimal value!");
            return;
        }
        auto const storage_slot_key = to_triedb_key(
            byte_string_view{storage_slot.value()}, storage_already_hashed);
        auto const storage_key =
            concat(NibblesView{account_key}, NibblesView{storage_slot_key});
        auto const storage_query_res = sm.lookup(storage_key);
        if (!storage_query_res) {
            fmt::println(
                "Could not find storage slot {} ({}) associated with account "
                "{}",
                NibblesView{storage_slot_key},
                storage,
                account,
                storage_query_res.error().message().c_str());
            return;
        }
        auto storage_encoded = storage_query_res.value().node->value();
        auto const storage_res = decode_storage_db(storage_encoded);
        if (!storage_res) {
            fmt::println(
                "Could not decode storage data from TrieDb -- {}",
                storage_res.error().message().c_str());
            return;
        }

        print_storage(storage_res.value().first, storage_res.value().second);
    }
}

void do_get_receipt(DbStateMachine &sm, std::string_view const receipt)
{
    size_t receipt_id{};

    if (receipt.starts_with("0x")) {
        fmt::println("Receipts should be entered in base 10 and will be "
                     "encoded for you.");
        return;
    }
    auto [_, ec] = std::from_chars(
        receipt.data(), receipt.data() + receipt.size(), receipt_id);
    if (ec != std::errc()) {
        fmt::println("Receipt must be an unsigned integer!");
        return;
    }
    auto const receipt_id_encoded = rlp::encode_unsigned(receipt_id);
    auto const receipt_query_res = sm.lookup(NibblesView{receipt_id_encoded});
    if (!receipt_query_res) {
        fmt::println(
            "Could not find receipt {} -- {}",
            receipt,
            receipt_query_res.error().message().c_str());
        return;
    }
    auto receipt_encoded = receipt_query_res.value().node->value();
    auto const receipt_res = decode_receipt_db(receipt_encoded);
    if (!receipt_res) {
        fmt::println(
            "Could not decode receipt -- {}",
            receipt_res.error().message().c_str());
    }
    auto const decoded = receipt_res.value().first;
    print_receipt(decoded);
}

std::optional<Nibbles>
domain_index_key(std::string_view const input, uint64_t &domain_id)
{
    auto const separator = input.find(':');
    if (separator == std::string_view::npos) {
        return std::nullopt;
    }
    domain_id = 0;
    size_t index{};
    auto const domain = input.substr(0, separator);
    auto const ix = input.substr(separator + 1);
    auto const domain_result = std::from_chars(
        domain.data(), domain.data() + domain.size(), domain_id);
    auto const ix_result =
        std::from_chars(ix.data(), ix.data() + ix.size(), index);
    if (domain_result.ec != std::errc{} ||
        domain_result.ptr != domain.data() + domain.size() ||
        ix_result.ec != std::errc{} || ix_result.ptr != ix.data() + ix.size()) {
        return std::nullopt;
    }
    uint8_t bytes[sizeof(domain_id)];
    intx::be::store(bytes, domain_id);
    return concat(
        NibblesView{to_byte_string_view(bytes)},
        NibblesView{rlp::encode_unsigned(index)});
}

void do_get_domain_receipt(DbStateMachine &sm, std::string_view const input)
{
    uint64_t domain_id;
    auto key = domain_index_key(input, domain_id);
    if (!key) {
        fmt::println("Use domain_id:index");
        return;
    }
    if (!sm.has_domain_block(domain_id)) {
        fmt::println("Could not find domain receipt {}", input);
        return;
    }
    auto result = sm.lookup(*key);
    if (!result) {
        fmt::println("Could not find domain receipt {}", input);
        return;
    }
    auto encoded = result.value().node->value();
    auto decoded = decode_receipt_db(encoded);
    if (!decoded || !encoded.empty()) {
        fmt::println("Could not decode domain receipt");
        return;
    }
    print_receipt(decoded.value().first);
}

void do_get_domain_transaction(DbStateMachine &sm, std::string_view const input)
{
    uint64_t domain_id;
    auto key = domain_index_key(input, domain_id);
    if (!key) {
        fmt::println("Use domain_id:index");
        return;
    }
    if (!sm.has_domain_block(domain_id)) {
        fmt::println("Could not find domain transaction {}", input);
        return;
    }
    auto result = sm.lookup(*key);
    if (!result) {
        fmt::println("Could not find domain transaction {}", input);
        return;
    }
    auto encoded = result.value().node->value();
    auto decoded = decode_transaction_db(encoded);
    if (!decoded || !encoded.empty()) {
        fmt::println("Could not decode domain transaction");
        return;
    }
    print_transaction(decoded.value().first, decoded.value().second);
}

std::optional<Nibbles> domain_hash_key(std::string_view const input)
{
    auto const separator = input.find(':');
    if (separator == std::string_view::npos) {
        return std::nullopt;
    }
    uint64_t domain_id{};
    auto const domain = input.substr(0, separator);
    auto const hash_text = input.substr(separator + 1);
    auto const domain_result = std::from_chars(
        domain.data(), domain.data() + domain.size(), domain_id);
    auto hash = from_hex(hash_text);
    if (domain_result.ec != std::errc{} ||
        domain_result.ptr != domain.data() + domain.size() ||
        !hash.has_value() || hash->size() != sizeof(hash256)) {
        return std::nullopt;
    }
    uint8_t domain_bytes[sizeof(domain_id)];
    intx::be::store(domain_bytes, domain_id);
    return concat(
        NibblesView{to_byte_string_view(domain_bytes)}, NibblesView{*hash});
}

void do_get_domain_transaction_hash(
    DbStateMachine &sm, std::string_view const input)
{
    auto key = domain_hash_key(input);
    if (!key) {
        fmt::println("Use domain_id:0x<32-byte transaction hash>");
        return;
    }
    auto result = sm.lookup(*key);
    if (!result) {
        fmt::println("Could not find domain transaction hash {}", input);
        return;
    }
    auto encoded = result.value().node->value();
    auto location = decode_transaction_location_db(encoded);
    if (!location || !encoded.empty()) {
        fmt::println("Could not decode domain transaction hash location");
        return;
    }
    fmt::println(
        "Block={} Index={}", location.value().first, location.value().second);
}

void do_get_transaction(DbStateMachine &sm, std::string_view const input)
{
    size_t transaction_id{};
    auto const parse = std::from_chars(
        input.data(), input.data() + input.size(), transaction_id);
    if (input.starts_with("0x") || parse.ec != std::errc{} ||
        parse.ptr != input.data() + input.size()) {
        fmt::println("Transaction must be an unsigned base-10 integer!");
        return;
    }
    auto const key = rlp::encode_unsigned(transaction_id);
    auto result = sm.lookup(NibblesView{key});
    if (!result) {
        fmt::println("Could not find transaction {}", input);
        return;
    }
    auto encoded = result.value().node->value();
    auto decoded = decode_transaction_db(encoded);
    if (!decoded || !encoded.empty()) {
        fmt::println("Could not decode transaction");
        return;
    }
    print_transaction(decoded.value().first, decoded.value().second);
}

void do_node_stats(DbStateMachine &sm)
{
    std::unordered_map<std::vector<bool>, size_t> metadata;

    class Traverse final : public TraverseMachine
    {
        std::unordered_map<std::vector<bool>, size_t> &metadata_;
        std::vector<bool> had_values_;

    public:
        explicit Traverse(
            std::unordered_map<std::vector<bool>, size_t> &metadata)
            : metadata_{metadata}
        {
        }

        Traverse(Traverse const &other) = default;

        virtual bool down(unsigned char const, Node const &node) override
        {
            had_values_.push_back(node.has_value());
            ++metadata_[had_values_];
            return true;
        }

        virtual void up(unsigned char const, Node const &) override
        {
            had_values_.pop_back();
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<Traverse>(*this);
        }
    } traverse(metadata);

    auto cursor_res = sm.db.find(
        concat(sm.curr_section_prefix, sm.curr_table_id), sm.curr_version);
    if (cursor_res.has_value()) {
        if (sm.db.traverse(cursor_res.value(), traverse, sm.curr_version) ==
            false) {
            fmt::println(
                "WARNING: Traverse finished early because version {} got "
                "pruned from db history",
                sm.curr_version);
            return;
        }
    }
    else {
        fmt::println(
            "Error: can't start traverse because current version {} already "
            "got pruned from db history",
            sm.curr_version);
        return;
    }

    std::vector<std::pair<size_t, std::vector<bool>>> sorted_metadata;
    size_t total{0};
    size_t leaves{0};
    size_t branches{0};
    for (auto const &[had_values, count] : metadata) {
        sorted_metadata.emplace_back(count, had_values);
        total += count;
        if (had_values.back()) {
            leaves += count;
        }
        else {
            branches += count;
        }
    }
    std::ranges::sort(sorted_metadata, std::ranges::greater());

    fmt::println(
        "Statistics:\nTotal={}\nLeaves={}\nBranches={}\n",
        total,
        leaves,
        branches);
    if (total > 0) {
        std::string out;
        for (auto const &[count, had_values] : sorted_metadata) {
            for (bool const has_value : had_values) {
                out += has_value ? "L" : "B";
            }
            fmt::format_to(
                std::back_inserter(out),
                ",{},{},{},{:.2f}%\n",
                had_values.size(),
                std::ranges::count(had_values, true),
                count,
                ((double)count / (double)total) * 100);
        }
        fmt::println("path,depth,leaves,count,percentage");
        fmt::println("{}", out);
    }
}

int interactive_impl(Db &db)
{
    if (!isatty(STDIN_FILENO)) {
        fmt::println("Not running interactively! Pass -it to run inside a "
                     "docker container.");
        return 1;
    }

    DbStateMachine state_machine{db};
    std::string line;

    print_help();

    while (true) {
        fmt::print("(monaddb) ");
        if (!std::getline(std::cin, line)) {
            fmt::print("\n");
            break;
        }

        auto const tokens = tokenize(line);
        if (tokens.empty()) {
            continue;
        }

        auto const begin = std::chrono::steady_clock::now();
        if (tokens[0] == "help") {
            print_help();
        }
        else if (tokens[0] == "version") {
            if (tokens.size() == 2) {
                do_version(state_machine, tokens[1]);
            }
            else {
                fmt::println(
                    "Wrong format to set version, type 'version [number]'");
            }
        }
        else if (tokens[0] == "list") {
            state_machine.list_finalized_and_proposals(
                state_machine.curr_version);
        }
        else if (tokens[0] == "proposal") {
            if (tokens.size() == 2) {
                do_proposal(state_machine, tokens[1]);
            }
            else {
                fmt::println("Wrong format to set proposal, type 'proposal "
                             "[block_id]'");
            }
        }
        else if (tokens[0] == "finalized") {
            state_machine.set_proposal_or_finalized(bytes32_t{});
        }
        else if (tokens[0] == "table") {
            if (tokens.size() == 2) {
                do_table(state_machine, tokens[1]);
            }
            else {
                fmt::println(
                    "Wrong format to set table; see `help` for table names.");
            }
        }
        else if (tokens[0] == "domain_root") {
            uint64_t domain_id{};
            auto const parse = tokens.size() == 2
                                   ? std::from_chars(
                                         tokens[1].data(),
                                         tokens[1].data() + tokens[1].size(),
                                         domain_id)
                                   : std::from_chars_result{};
            if (tokens.size() != 2 || parse.ec != std::errc{} ||
                parse.ptr != tokens[1].data() + tokens[1].size()) {
                fmt::println("Use domain_root [decimal domain id]");
            }
            else {
                state_machine.print_domain_root(domain_id);
            }
        }
        else if (tokens[0] == "get") {
            if (state_machine.curr_table_id == INVALID_NIBBLE) {
                fmt::println(
                    "Need to set a table id before calling \"get\". See "
                    "`help` for details");
            }
            else if (tokens.size() != 2 && tokens.size() != 3) {
                fmt::println("No key provided.");
            }
            else if (state_machine.curr_table_id == STATE_NIBBLE) {
                do_get_account(
                    state_machine,
                    tokens[1],
                    tokens.size() > 2 ? tokens[2] : "");
            }
            else if (state_machine.curr_table_id == CODE_NIBBLE) {
                do_get_code(state_machine, tokens[1]);
            }
            else if (state_machine.curr_table_id == RECEIPT_NIBBLE) {
                do_get_receipt(state_machine, tokens[1]);
            }
            else if (state_machine.curr_table_id == TRANSACTION_NIBBLE) {
                do_get_transaction(state_machine, tokens[1]);
            }
            else if (state_machine.curr_table_id == DOMAIN_RECEIPT_NIBBLE) {
                do_get_domain_receipt(state_machine, tokens[1]);
            }
            else if (state_machine.curr_table_id == DOMAIN_TRANSACTION_NIBBLE) {
                do_get_domain_transaction(state_machine, tokens[1]);
            }
            else if (state_machine.curr_table_id == DOMAIN_TX_HASH_NIBBLE) {
                do_get_domain_transaction_hash(state_machine, tokens[1]);
            }
        }
        else if (tokens[0] == "node_stats") {
            if (state_machine.curr_table_id == INVALID_NIBBLE) {
                fmt::println(
                    "Need to set a table id before calling \"node_stats\". "
                    "See `help` for details");
                continue;
            }
            do_node_stats(state_machine);
        }
        else if (tokens[0] == "back") {
            state_machine.back();
        }
        else if (tokens[0] == "quit" || tokens[0] == "exit") {
            // TODO key stroke exit anyway? (y or n)
            break;
        }
        else {
            fmt::println("Invalid command: \"{}\". See \"help\"", tokens[0]);
        }
        fmt::println("Took {}", std::chrono::steady_clock::now() - begin);
    }
    return 0;
}

// Resolve a --version spec to a concrete block version. The spec is either a
// decimal block number or the literal "latest_finalized". Returns nullopt on a
// malformed spec.
std::optional<uint64_t> resolve_snapshot_version(
    std::string const &spec, uint64_t const latest_finalized)
{
    if (spec == "latest_finalized") {
        return latest_finalized;
    }
    uint64_t value;
    auto const [ptr, ec] =
        std::from_chars(spec.data(), spec.data() + spec.size(), value);
    if (ec != std::errc{} || ptr != spec.data() + spec.size()) {
        return std::nullopt;
    }
    return value;
}

MONAD_ANONYMOUS_NAMESPACE_END

int main(int const argc, char *argv[])
{
    std::vector<std::filesystem::path> dbname_paths;
    std::optional<unsigned> sq_thread_cpu = std::nullopt;
    auto log_level = quill::LogLevel::Info;
    bool interactive = false;
    std::optional<std::filesystem::path> dump_binary_snapshot;
    std::optional<std::filesystem::path> load_binary_snapshot;
    std::optional<std::filesystem::path> dump_state_path;
    std::string version;
    unsigned dump_concurrency_limit = 2048;
    bool use_secondary = false;
    uint64_t total_shards = 1;
    uint64_t shard_number = 0;

    CLI::App cli{
        "Inspection and snapshot tooling for a Monad execution database.",
        "monad-cli"};
    monad::cli::HelpFormatter{GIT_COMMIT_HASH}.install(cli);
    cli.add_option(
           "--db",
           dbname_paths,
           "A comma-separated list of previously created database paths")
        ->required();
    cli.add_option(
        "--sq-thread-cpu,--sq_thread_cpu",
        sq_thread_cpu,
        "CPU core binding for the io_uring SQPOLL thread. Specifies the CPU "
        "set for the kernel polling thread in SQPOLL mode. Defaults to "
        "disabled SQPOLL mode.");
    cli.add_option("--log-level,--log_level", log_level, "level of logging")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    auto *const mode_group =
        cli.add_option_group("mode", "different modes of the cli");
    mode_group->add_flag(
        "--it,--interactive", interactive, "set to run in interactive mode");
    auto *const cli_group =
        mode_group->add_option_group("cli", "options for non-interactive mode");
    cli_group
        ->add_option(
            "--version",
            version,
            "Block version to operate on: a block number, or "
            "\"latest_finalized\" to use the database's latest finalized "
            "version")
        ->required();
    auto *const dump_binary_snapshot_option = cli_group->add_option(
        "--dump-binary-snapshot,--dump_binary_snapshot",
        dump_binary_snapshot,
        "Dump a binary snapshot to directory");
    cli_group->add_option(
        "--dump-concurrency-limit,--dump_concurrency_limit",
        dump_concurrency_limit,
        "Read concurrency limit for snapshot dump");
    cli_group
        ->add_option(
            "--total-shards,--total_shards",
            total_shards,
            "Total number of shards to split snapshot creation across nodes "
            "(default: 1)")
        ->check(CLI::Range(1u, MONAD_SNAPSHOT_SHARDS))
        ->needs(dump_binary_snapshot_option);
    cli_group
        ->add_option(
            "--shard-number,--shard_number",
            shard_number,
            "Shard number for this node (0 to total_shards-1, default: 0). "
            "Each "
            "shard writes its portion of data and headers.")
        ->needs(dump_binary_snapshot_option);
    auto *const load_binary_snapshot_option =
        cli_group
            ->add_option(
                "--load-binary-snapshot,--load_binary_snapshot",
                load_binary_snapshot,
                "Load a binary snapshot to db")
            ->check(CLI::ExistingDirectory)
            ->excludes(dump_binary_snapshot_option);
    cli_group
        ->add_option(
            "--dump-state,--dump_state",
            dump_state_path,
            "Dump the full state at --version as JSON to this path")
        ->excludes(dump_binary_snapshot_option)
        ->excludes(load_binary_snapshot_option);
    cli.add_flag(
        "--secondary",
        use_secondary,
        "Operate on the secondary timeline instead of the primary: --it opens "
        "it read-only, --dump-binary-snapshot dumps from it, and "
        "--load-binary-snapshot loads into it. The secondary must already be "
        "active with its state_machine_kind stamped (via monad-mpt "
        "--activate-secondary --state-machine).");
    mode_group->require_option(0, 1);
    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        return cli.exit(e);
    }
    catch (CLI::RequiredError const &e) {
        return cli.exit(e);
    }
    catch (CLI::ParseError const &e) {
        return cli.exit(e);
    }

    init_root_logger(log_level);
    LOG_INFO("running with commit '{}'", GIT_COMMIT_HASH);
    flush_logger();

    // Validate snapshot-dump preconditions before opening the database or
    // starting any work, so a misconfigured environment fails immediately with
    // a non-zero exit code rather than part-way through (which would leave a
    // partial snapshot behind).
    if (dump_binary_snapshot.has_value()) {
        if (shard_number >= total_shards) {
            LOG_ERROR(
                "shard_number ({}) must be < total_shards ({})",
                shard_number,
                total_shards);
            return 1;
        }
        // The dumper processes the shard indices s in [0,
        // MONAD_SNAPSHOT_SHARDS) with s % total_shards == shard_number (see
        // db_snapshot.cpp), so this run handles ceil((SHARDS - shard_number) /
        // total_shards) shards. The ternary guards the unsigned subtraction
        // against shard_number >= SHARDS (no shards match, count is 0).
        uint64_t const shards_this_run =
            shard_number < MONAD_SNAPSHOT_SHARDS
                ? (MONAD_SNAPSHOT_SHARDS - shard_number + total_shards - 1) /
                      total_shards
                : 0;
        // The dumper holds one fd open per (shard, data file) for the whole
        // run; add headroom for the triedb device(s), io_uring rings, logger,
        // and std streams.
        constexpr uint64_t fd_headroom = 256;
        uint64_t const required_fds =
            shards_this_run * MONAD_SNAPSHOT_FILES_PER_SHARD + fd_headroom;
        struct rlimit limit{};
        if (getrlimit(RLIMIT_NOFILE, &limit) != 0) {
            // getrlimit essentially never fails for RLIMIT_NOFILE; if it
            // somehow does we cannot verify the limit, so warn and proceed
            // rather than block a dump that may well succeed. The dumper's
            // open() asserts remain the backstop.
            LOG_WARNING(
                "could not read the open file descriptor limit (getrlimit "
                "failed: {}); proceeding without the snapshot fd pre-flight "
                "check",
                std::strerror(errno));
        }
        else if (limit.rlim_cur < required_fds) {
            // The soft limit was already raised toward the hard limit at
            // startup (AsyncIO_rlimit_raiser in category/async/io.cpp), so
            // reaching here means the hard limit itself is too low and must be
            // raised (limits.conf / systemd LimitNOFILE).
            auto const hard_limit = limit.rlim_max == RLIM_INFINITY
                                        ? std::string{"unlimited"}
                                        : std::to_string(limit.rlim_max);
            LOG_ERROR(
                "open file descriptor limit (soft {}, hard {}) is too low to "
                "dump this snapshot, which needs about {} descriptors ({} "
                "shards x {} files plus headroom). Raise the hard limit for "
                "this user (e.g. add '<user> hard nofile 16384' to "
                "/etc/security/limits.conf, or set LimitNOFILE in the systemd "
                "unit) and retry.",
                limit.rlim_cur,
                hard_limit,
                required_fds,
                shards_this_run,
                MONAD_SNAPSHOT_FILES_PER_SHARD);
            return 1;
        }
    }

    uint64_t resolved_version = 0;
    {
        fmt::println("Opening read only database {}.", dbname_paths);
        ReadOnlyOnDiskDbConfig const ro_config{
            .sq_thread_cpu = sq_thread_cpu, .dbname_paths = dbname_paths};
        AsyncIOContext io_ctx{ro_config};
        Db ro_db{
            io_ctx,
            use_secondary ? timeline_id::secondary : timeline_id::primary};
        fmt::println(
            "db summary: earliest_block_id={} latest_block_id={} "
            "latest_finalized_block_id={} last_verified_block_id={} "
            "history_length={}",
            ro_db.get_earliest_version(),
            ro_db.get_latest_version(),
            ro_db.get_latest_finalized_version(),
            ro_db.get_latest_verified_version(),
            ro_db.get_history_length());
        if (interactive) {
            return interactive_impl(ro_db);
        }
        if (dump_binary_snapshot.has_value() ||
            load_binary_snapshot.has_value() || dump_state_path.has_value()) {
            auto const v = resolve_snapshot_version(
                version, ro_db.get_latest_finalized_version());
            if (!v.has_value()) {
                LOG_ERROR(
                    "invalid --version \"{}\": expected a block number or "
                    "\"latest_finalized\"",
                    version);
                return 1;
            }
            if (*v == INVALID_BLOCK_NUM) {
                LOG_ERROR(
                    "no finalized version available to snapshot (the database "
                    "has no finalized blocks)");
                return 1;
            }
            resolved_version = *v;
        }
        if (dump_state_path.has_value()) {
            return dump_state_to_file(
                ro_db, resolved_version, dump_state_path.value());
        }
    }
    if (dump_binary_snapshot.has_value()) {
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                dump_binary_snapshot.value().c_str(), resolved_version);
        std::vector<char const *> c_dbname_paths;
        for (auto const &path : dbname_paths) {
            c_dbname_paths.emplace_back(path.c_str());
        }
        [[maybe_unused]] auto const begin = std::chrono::steady_clock::now();
        bool const success = monad_db_dump_snapshot(
            c_dbname_paths.data(),
            c_dbname_paths.size(),
            sq_thread_cpu.value_or(std::numeric_limits<unsigned>::max()),
            resolved_version,
            monad_db_snapshot_write_filesystem,
            context,
            dump_concurrency_limit,
            total_shards,
            shard_number,
            use_secondary);
        // Finalize (flush/close the data files and write the checksums) before
        // logging success: destroy asserts on a write/checksum failure, so
        // doing it first keeps a late failure from being preceded by a
        // success=true log line.
        monad_db_snapshot_filesystem_write_user_context_destroy(context);
        LOG_INFO(
            "snapshot dump success={} version={} directory={} "
            "dump_from_secondary={} elapsed={}",
            success,
            resolved_version,
            dump_binary_snapshot.value(),
            use_secondary,
            std::chrono::steady_clock::now() - begin);
        return success == false;
    }
    else if (load_binary_snapshot.has_value()) {
        std::vector<char const *> c_dbname_paths;
        for (auto const &path : dbname_paths) {
            c_dbname_paths.emplace_back(path.c_str());
        }
        [[maybe_unused]] auto const begin = std::chrono::steady_clock::now();
        monad_db_snapshot_load_filesystem(
            c_dbname_paths.data(),
            c_dbname_paths.size(),
            sq_thread_cpu.value_or(std::numeric_limits<unsigned>::max()),
            load_binary_snapshot.value().c_str(),
            resolved_version,
            use_secondary);
        LOG_INFO(
            "snapshot version={} load_binary_snapshot={} load_to_secondary={} "
            "elapsed={}",
            resolved_version,
            load_binary_snapshot.value(),
            use_secondary,
            std::chrono::steady_clock::now() - begin);
    }
    return 0;
}
