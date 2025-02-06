#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp> // NOLINT
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/account_fmt.hpp> // NOLINT
#include <monad/core/fmt/bytes_fmt.hpp> // NOLINT
#include <monad/core/fmt/receipt_fmt.hpp> // NOLINT
#include <monad/core/keccak.h>
#include <monad/core/keccak.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/core/rlp/receipt_rlp.hpp>
#include <monad/db/util.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/nibbles_view_fmt.hpp> // NOLINT
#include <monad/mpt/node_cursor.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/util.hpp>

#include <CLI/CLI.hpp>
#include <evmc/hex.hpp>
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
#include <span>
#include <spanstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

#include <stdio.h>
#include <unistd.h>

using namespace monad;
using namespace monad::mpt;

namespace
{
    ////////////////////////////////////////
    // CLI input parsing helpers
    ////////////////////////////////////////

    bool is_numeric(std::string_view str)
    {
        return !str.empty() && std::all_of(str.begin(), str.end(), ::isdigit);
    }

    std::vector<std::string> tokenize(std::string_view input, char delim = ' ')
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
        return already_hashed
                   ? byte_string{input.data(), input.size()}
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
                       "0x{:02x}",
                       fmt::join(std::as_bytes(std::span(code)), ""))));
    }
}

struct DbStateMachine
{
    Db &db;

    uint64_t curr_version{INVALID_BLOCK_ID};
    std::optional<uint64_t> curr_round{}; // nullopt means finalized
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
        MONAD_ASSERT(version != INVALID_BLOCK_ID);
        if (state != DbState::unset) {
            fmt::println(
                "Error: already at version {}, use 'back' to move cursor "
                "up and try again",
                curr_version);
            return;
        }
        MONAD_ASSERT(curr_version == INVALID_BLOCK_ID);
        MONAD_ASSERT(curr_section_prefix.nibble_size() == 0);

        auto const min_version = db.get_earliest_block_id();
        auto const max_version = db.get_latest_block_id();
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
            fmt::println("Type \"proposal [round]\" or "
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
        if (version == INVALID_BLOCK_ID) {
            fmt::println("Error: invalid version to list sections, set to a "
                         "valid version and try again");
            return false;
        }
        auto const finalized_res = db.find(finalized_nibbles, version);
        auto rounds = get_proposal_rounds(db, version);
        if (finalized_res.has_error() && rounds.empty()) {
            return false;
        }
        std::sort(rounds.begin(), rounds.end());
        fmt::println("List sections of version {}: ", version);
        if (finalized_res.has_value()) {
            fmt::println("    finalized : yes ", version);
        }
        else {
            fmt::println("    finalized : no ", version);
        }
        fmt::println("    proposals : {}\n", rounds);
        return true;
    }

    void set_proposal_or_finalized(std::optional<uint64_t> const round)
    {
        if (state != DbState::version_number) {
            fmt::println("Error: at wrong part of trie, only allow set section "
                         "when cursor is set to a version.");
            return;
        }
        MONAD_ASSERT(curr_section_prefix.nibble_size() == 0);
        if (round.has_value()) { // set proposal
            auto const prefix = proposal_prefix(round.value());
            if (db.find(prefix, curr_version).has_value()) {
                curr_section_prefix = prefix;
                curr_round = round;
                state = DbState::proposal_or_finalize;
                fmt::println(
                    "Success! Set to proposal {} of version {}",
                    round.value(),
                    curr_version);
            }
            else {
                fmt::println("Could not locate round {}", round.value());
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
            if (curr_round.has_value()) {
                fmt::println(
                    "At proposal round {} of version {}",
                    curr_round.value(),
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
            curr_round = std::nullopt;
            fmt::println(
                "At version {}. Type \"proposal [round]\" or "
                "\"finalized\" to set section",
                curr_version);
            break;
        case DbState::version_number:
            curr_version = INVALID_BLOCK_ID;
            state = DbState::unset;
            fmt::println("Version is unset");
            break;
        default:
            curr_version = INVALID_BLOCK_ID;
        }
        curr_table_id = INVALID_NIBBLE;
    }
};

void print_db_version_info(Db &db)
{
    auto const min_version = db.get_earliest_block_id();
    auto const max_version = db.get_latest_block_id();
    if (min_version != INVALID_BLOCK_ID && max_version != INVALID_BLOCK_ID) {
        fmt::println(
            "Database is open with minimum version {} and maximum version {},\n"
            "latest finalized version {}, latest verified version {}",
            min_version,
            max_version,
            db.get_latest_finalized_block_id(),
            db.get_latest_verified_block_id());
    }
    else {
        throw std::runtime_error("This is an empty Db that contains no valid "
                                 "versions, try a different db");
    }
}

////////////////////////////////////////
// Command actions
////////////////////////////////////////

void print_help()
{
    fmt::print(
        "List of commands:\n\n"
        "version [version_number]     -- Set the database version\n"
        "proposal [round_number] or finalized -- Set the section to query\n"
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

void do_proposal(DbStateMachine &sm, std::string_view const round)
{
    uint64_t r{};
    auto [_, ec] =
        std::from_chars(round.data(), round.data() + round.size(), r);
    if (ec != std::errc()) {
        fmt::println("Invalid round: please input a number.");
    }
    else {
        sm.set_proposal_or_finalized(r);
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
    struct DepthMetadata
    {
        uint32_t node_count;
        uint32_t leaf_count;
        uint32_t branch_count;
        std::vector<uint32_t> nibble_depth;
    };

    using TrieMetadata = std::vector<DepthMetadata>;
    TrieMetadata metadata;

    struct Traverse final : public TraverseMachine
    {
        TrieMetadata &metadata;
        unsigned nibble_depth;
        unsigned depth;
        NibblesView const root;

        Traverse(TrieMetadata &metadata_, NibblesView const root_ = {})
            : metadata{metadata_}
            , nibble_depth{0}
            , depth{0}
            , root{root_}
        {
        }

        Traverse(Traverse const &other) = default;

        virtual bool down(unsigned char const branch, Node const &node) override
        {
            if (branch == INVALID_BRANCH) {
                note(node);
                return true;
            }

            ++depth;
            nibble_depth += 1 + node.path_nibble_view().nibble_size();
            note(node);
            return true;
        }

        virtual void up(unsigned char const branch, Node const &node) override
        {
            if (branch == INVALID_BRANCH) {
                return;
            }
            unsigned const subtrahend =
                1 + node.path_nibble_view().nibble_size();
            MONAD_ASSERT(nibble_depth >= subtrahend);
            nibble_depth -= subtrahend;
            --depth;
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<Traverse>(*this);
        }

        void note(Node const &node)
        {
            metadata.resize(
                std::max(metadata.size(), static_cast<size_t>(depth) + 1));

            ++metadata[depth].node_count;
            metadata[depth].leaf_count +=
                static_cast<uint32_t>(node.value_len > 0);
            metadata[depth].branch_count +=
                static_cast<uint32_t>(node.number_of_children() > 0);
            metadata[depth].nibble_depth.emplace_back(nibble_depth);
        }
    } traverse(metadata, concat(sm.curr_table_id));

    auto cursor_res = sm.db.find(
        concat(sm.curr_section_prefix, sm.curr_table_id), sm.curr_version);
    if (cursor_res.has_value()) {
        if (sm.db.traverse(cursor_res.value(), traverse, sm.curr_version) ==
            false) {
            fmt::println(
                "WARNING: Traverse finished early because version {} got "
                "pruned from db history",
                sm.curr_version);
        }
    }
    else {
        fmt::println(
            "Error: can't start traverse because current version {} already "
            "got pruned from db history",
            sm.curr_version);
    }

    auto agg_stats = [](std::vector<uint32_t> const &data)
        -> std::tuple<size_t, double, double> {
        auto const size = static_cast<double>(data.size());
        if (size == 0) {
            return std::make_tuple(size, NAN, NAN);
        }
        double const mean =
            std::accumulate(data.begin(), data.end(), 0.0) / size;

        double const pop_var = std::accumulate(
                                   data.begin(),
                                   data.end(),
                                   0.0,
                                   [mean](double acc, uint32_t const val) {
                                       double const dev = val - mean;
                                       return acc + dev * dev;
                                   }) /
                               size;

        return std::make_tuple(size, mean, sqrt(pop_var));
    };

    fmt::println(
        "{:>5} {:>15} {:>15} {:>15} {:>20}",
        "depth",
        "# nodes",
        "# leaves",
        "# branches",
        "nibble depth");
    auto format_mean = [](double mean, double stddev) {
        return std::isnan(mean) ? "N/A"
                                : fmt::format("{:.2f} (±{:.2f})", mean, stddev);
    };
    for (unsigned depth = 0; depth < metadata.size(); ++depth) {
        auto [_, mean_nd, stddev_nd] = agg_stats(metadata[depth].nibble_depth);
        fmt::println(
            "{:>5} {:>15} {:>15} {:>15} {:>20}",
            depth,
            metadata[depth].node_count,
            metadata[depth].leaf_count,
            metadata[depth].branch_count,
            format_mean(mean_nd, stddev_nd));
    }
}

int interactive_impl(Db &db)
{
    DbStateMachine state_machine{db};
    std::string line;

    print_db_version_info(db);
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
                             "[round number]'");
            }
        }
        else if (tokens[0] == "finalized") {
            state_machine.set_proposal_or_finalized(std::nullopt);
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

int main(int argc, char *argv[])
{
    std::vector<std::filesystem::path> dbname_paths{"test.db"};

    CLI::App cli{"monad_cli"};
    cli.add_option(
           "--db",
           dbname_paths,
           "A comma-separated list of previously created database paths")
        ->required();
    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        return cli.exit(e);
    }
    catch (CLI::RequiredError const &e) {
        return cli.exit(e);
    }

    if (!isatty(STDIN_FILENO)) {
        fmt::println("Not running interactively! Pass -it to run inside a "
                     "docker container.");
        return 1;
    }

    ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = dbname_paths};

    Db ro_db{ro_config};

    fmt::print("Opening read only database ");
    for (auto const &dbname : dbname_paths) {
        fmt::print(" {}", dbname);
    }
    fmt::println(".");

    return interactive_impl(ro_db);
}
