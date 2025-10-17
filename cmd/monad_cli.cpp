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
#include <category/core/config.hpp>
#include <category/core/keccak.h>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/fmt/account_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/fmt/receipt_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/log_level_map.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/receipt_rlp.hpp>
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
#include <evmc/hex.hpp>
#include <quill/Quill.h>
#include <quill/bundled/fmt/core.h>
#include <quill/bundled/fmt/format.h>

#include <algorithm>
#include <cctype>
#include <charconv>
#include <chrono>
#include <cmath>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <memory>
#include <numeric>
#include <ranges>
#include <span>
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
#include <unistd.h>

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

////////////////////////////////////////
// CLI input parsing helpers
////////////////////////////////////////

bool is_numeric(std::string_view str)
{
    return !str.empty() && std::all_of(str.begin(), str.end(), ::isdigit);
}

std::vector<std::string> tokenize(std::string_view input, char delim = ' ')
{
    std::vector<std::string> tokens;
    size_t start = 0;
    while (start < input.size()) {
        size_t const next = input.find(delim, start);
        size_t const count =
            (next == std::string_view::npos) ? input.size() - start
                                             : next - start;
        if (count != 0) {
            tokens.emplace_back(input.substr(start, count));
        }
        if (next == std::string_view::npos) {
            break;
        }
        start = next + 1;
    }
    return tokens;
}

////////////////////////////////////////
// TrieDb Helpers
////////////////////////////////////////

std::string_view table_as_string(unsigned char table_id)
{
    switch (table_id) {
    case STATE_NIBBLE:
        return "state";
    case CODE_NIBBLE:
        return "code";
    case RECEIPT_NIBBLE:
        return "receipt";
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

void print_storage(bytes32_t key, bytes32_t val)
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

    void set_table(unsigned char table_id)
    {
        if (state != DbState::proposal_or_finalize) {
            fmt::println("Error: at wrong part of trie, only allow set table "
                         "when cursor is set to a specific version number.");
            return;
        }
        MONAD_ASSERT(curr_section_prefix.nibble_size() > 0);

        if (table_id == STATE_NIBBLE || table_id == CODE_NIBBLE ||
            table_id == RECEIPT_NIBBLE) {
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
            }
        }
        else {
            fmt::println("Invalid table id: choose table id from 0: state, "
                         "1: code, 2: receipt.");
        }
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
        "table [state/receipt/code]   -- Set the table to query\n"
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
    auto const code_hex = evmc::from_hex(code_hash);
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
    auto const account_hex = evmc::from_hex(account);
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
        auto const storage_slot = evmc::from_hex(normalized_storage);
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
                fmt::println("Wrong format to set table, type 'table "
                             "[state/code/receipt]'");
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

MONAD_ANONYMOUS_NAMESPACE_END

int main(int argc, char *argv[])
{
    std::vector<std::filesystem::path> dbname_paths;
    std::optional<unsigned> sq_thread_cpu = std::nullopt;
    auto log_level = quill::LogLevel::Info;
    bool interactive = false;
    std::optional<std::filesystem::path> dump_binary_snapshot;
    std::optional<std::filesystem::path> load_binary_snapshot;
    uint64_t version;

    CLI::App cli{"monad_cli"};
    cli.add_option(
           "--db",
           dbname_paths,
           "A comma-separated list of previously created database paths")
        ->required();
    cli.add_option(
        "--sq_thread_cpu",
        sq_thread_cpu,
        "CPU core binding for the io_uring SQPOLL thread. Specifies the CPU "
        "set for the kernel polling thread in SQPOLL mode. Defaults to "
        "disabled SQPOLL mode.");
    cli.add_option("--log_level", log_level, "level of logging")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    auto *const mode_group =
        cli.add_option_group("mode", "different modes of the cli");
    mode_group->add_flag(
        "--it,--interactive", interactive, "set to run in interactive mode");
    auto *const cli_group =
        mode_group->add_option_group("cli", "options for non-interactive mode");
    cli_group->add_option("--version", version)->required();
    auto *const dump_binary_snapshot_option = cli_group->add_option(
        "--dump_binary_snapshot",
        dump_binary_snapshot,
        "Dump a binary snapshot to directory");
    cli_group
        ->add_option(
            "--load_binary_snapshot",
            load_binary_snapshot,
            "Load a binary snapshot to db")
        ->check(CLI::ExistingDirectory)
        ->excludes(dump_binary_snapshot_option);
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

    auto stdout_handler = quill::stdout_handler();
    stdout_handler->set_pattern(
        "%(time) [%(thread_id)] %(file_name):%(line_number) LOG_%(log_level)\t"
        "%(message)",
        "%Y-%m-%d %H:%M:%S.%Qns",
        quill::Timezone::GmtTime);
    quill::Config cfg;
    cfg.default_handlers.emplace_back(stdout_handler);
    quill::configure(cfg);
    quill::start(true);
    quill::get_root_logger()->set_log_level(log_level);
    LOG_INFO("running with commit '{}'", GIT_COMMIT_HASH);
    quill::flush();

    {
        fmt::println("Opening read only database {}.", dbname_paths);
        ReadOnlyOnDiskDbConfig const ro_config{
            .sq_thread_cpu = sq_thread_cpu, .dbname_paths = dbname_paths};
        AsyncIOContext io_ctx{ro_config};
        Db ro_db{io_ctx};
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
    }
    if (dump_binary_snapshot.has_value()) {
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                dump_binary_snapshot.value().c_str(), version);
        std::vector<char const *> c_dbname_paths;
        for (auto const &path : dbname_paths) {
            c_dbname_paths.emplace_back(path.c_str());
        }
        [[maybe_unused]] auto const begin = std::chrono::steady_clock::now();
        bool const success = monad_db_dump_snapshot(
            c_dbname_paths.data(),
            c_dbname_paths.size(),
            sq_thread_cpu.value_or(std::numeric_limits<unsigned>::max()),
            version,
            monad_db_snapshot_write_filesystem,
            context);
        LOG_INFO(
            "snapshot dump success={} version={} directory={} elapsed={}",
            success,
            version,
            dump_binary_snapshot.value(),
            std::chrono::steady_clock::now() - begin);
        monad_db_snapshot_filesystem_write_user_context_destroy(context);
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
            version);
        LOG_INFO(
            "snapshot version={} load_binary_snapshot={} elapsed={}",
            version,
            load_binary_snapshot.value(),
            std::chrono::steady_clock::now() - begin);
    }
    return 0;
}
