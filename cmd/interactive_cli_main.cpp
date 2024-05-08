#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/result.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/db_error.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node_cursor.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/util.hpp>

#include <CLI/CLI.hpp>
#include <boost/outcome/try.hpp>
#include <evmc/hex.hpp>

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <span>
#include <stack>
#include <stdexcept>
#include <string>
#include <vector>

using namespace monad;
using namespace monad::mpt;

namespace
{
    constexpr unsigned char state_nibble = 0x0;
    constexpr unsigned char code_nibble = 0x1;
    constexpr unsigned char receipt_nibble = 0x2;
}

enum class DbSection : uint8_t
{
    root = 0,
    version_number,
    table,
    invalid
};

struct DbStateMachine
{
    static constexpr uint64_t INVALID_VERSION = uint64_t(-1);
    static constexpr unsigned char INVALID_TABLE_ID = 0xff;

    Db &db;
    uint64_t curr_version{INVALID_VERSION};
    unsigned char curr_table_id{INVALID_TABLE_ID};
    DbSection state{DbSection::root};
    std::stack<NodeCursor> cursors{};

    explicit DbStateMachine(Db &db)
        : db(db)
    {
        cursors.push(db.root());
    }

    bool check_version(uint64_t const version) const
    {
        auto const min_opt = db.get_earliest_block_id();
        auto const max_opt = db.get_latest_block_id();
        MONAD_ASSERT(min_opt.has_value() && max_opt.has_value());
        if (min_opt.value() > version || max_opt.value() < version) {
            std::cout << "Error: invalid version " << version
                      << ". Please chooose a valid version in range [ "
                      << min_opt.value() << ", " << max_opt.value() << " ]"
                      << std::endl;
            return false;
        }
        return true;
    }

    void set_version(uint64_t const version)
    {
        if (state != DbSection::root) {
            std::cout << "Error setting a new version: at wrong part of trie, "
                         "use 'back' to move the cursor back up and try again"
                      << std::endl;
            return;
        }
        if (!check_version(version)) {
            return;
        }
        std::cout << "Setting cursor to version " << version << "..."
                  << std::endl;
        auto res = db.get(
            db.root(), serialize_as_big_endian<BLOCK_NUM_BYTES>(version));
        if (res.has_error()) {
            std::cout << "Error setting the cursor" << std::endl;
            return;
        }
        std::cout << "Success! Next try set cursor to a specific table by "
                     "\"table [0/1/2]\""
                  << std::endl;
        cursors.push(res.assume_value());
        curr_version = version;
        state = DbSection::version_number;
    }

    void set_table(unsigned char table_id)
    {
        if (state != DbSection::version_number) {
            std::cout << "Error: at wrong part of trie, only allow set table "
                         "when cursor is set to a specific version number."
                      << std::endl;
            return;
        }

        if (table_id == state_nibble || table_id == code_nibble ||
            table_id == receipt_nibble) {
            std::cout << "Setting cursor to version " << curr_version
                      << " table " << (unsigned)table_id << "..." << std::endl;
            auto const res = db.get(cursors.top(), concat(table_id));
            if (res.has_value()) {
                cursors.push(res.assume_value());
                state = DbSection::table;
                curr_table_id = table_id;
                std::cout
                    << "Success! Next try look up a key in this table using "
                       "\"get [key]\""
                    << std::endl;
            }
            else {
                std::cout << "Error setting cursor to table "
                          << (unsigned)table_id << ": "
                          << res.error().message().c_str() << std::endl;
            }
        }
        else {
            std::cout << "Invalid table id: choose table id from 0: state, "
                         "1: code, 2: receipt."
                      << std::endl;
        }
    }

    void get_value(NibblesView const key)
    {
        if (state != DbSection::table) {
            std::cout << "Error: at wrong part of trie, please navigate cursor "
                         "to a table before lookup."
                      << std::endl;
        }
        std::cout << "Looking up key " << key << " at version " << curr_version
                  << " table " << curr_table_id << "..." << std::endl;

        auto res = db.get(cursors.top(), key);
        if (res.has_value()) {
            MONAD_ASSERT(res.value().is_valid());
            MONAD_ASSERT(res.value().node->has_value());
            std::cout << "Success! Value: " << res.value().node->value()
                      << std::endl;
        }
        else {
            std::cout << "Error: " << res.error().message().c_str()
                      << std::endl;
        }
    }

    void back()
    {
        switch (state) {
        case DbSection::table:
            state = DbSection::version_number;
            cursors.pop();
            std::cout << "Success! Cursor moved back to root of version "
                      << curr_version;
            break;
        case DbSection::version_number:
            curr_version = INVALID_VERSION;
            cursors.pop();
            state = DbSection::root;
            std::cout << "Success! Cursor moved back to root";
            break;
        case DbSection::root:
            std::cout
                << "No effect: cursor is currently at root of database trie";
            break;
        default:
            curr_version = INVALID_VERSION;
            state = DbSection::root;
            std::cout << "Cursor is at root";
        }
        std::cout << std::endl;
        curr_table_id = INVALID_TABLE_ID;
    }
};

void print_db_version_info(Db &db)
{
    if (auto const min_opt = db.get_earliest_block_id(); min_opt.has_value()) {
        auto const max_opt = db.get_latest_block_id();
        MONAD_ASSERT(max_opt.has_value());
        std::cout << "Database is open with minimum version " << min_opt.value()
                  << ", and maximum version " << max_opt.value() << std::endl;
    }
    else {
        throw std::runtime_error("This is an empty Db that contains no valid "
                                 "versions, try a different db");
    }
}

void print_help()
{
    std::cout
        << "List of commands:\n\n"
        << "version [version_number]  -- Set the database version\n"
        << "table [0/1/2]             -- Set the table (0: state, 1: code, 2: "
           "receipt)\n"
        << "get [key]                 -- Get the value for the given key\n"
        << "back                      -- Move back to the previous level\n"
        << "help                      -- Show this help message\n"
        << "exit                      -- Exit the program\n";
}

bool is_numeric(std::string const &str)
{
    return !str.empty() && std::all_of(str.begin(), str.end(), ::isdigit);
}

int interactive_impl(Db &db)
{
    DbStateMachine state_machine{db};
    std::string line;

    print_db_version_info(db);
    print_help();

    while (true) {
        std::cout << "(monaddb) ";
        std::getline(std::cin, line);

        if (line == "help") {
            print_help();
        }
        else if (line.substr(0, 8) == "version ") {
            auto const input = line.substr(8);
            if (!is_numeric(input)) {
                std::cout << "Invalid version: please input a number."
                          << std::endl;
                continue;
            }
            state_machine.set_version((uint64_t)std::atoll(input.c_str()));
        }
        else if (line.substr(0, 6) == "table ") {
            auto const input = line.substr(6);
            if (!is_numeric(input)) {
                std::cout << "Invalid table id: please input a number."
                          << std::endl;
                continue;
            }
            state_machine.set_table((unsigned char)std::atoi(input.c_str()));
        }
        else if (line.substr(0, 4) == "get ") {
            auto const res = evmc::from_hex(line.substr(4));
            if (res.has_value()) {
                state_machine.get_value(NibblesView{res.value()});
            }
            else {
                std::cout << "Invalid key." << std::endl;
            }
        }
        else if (line == "back") {
            state_machine.back();
        }
        else if (line == "exit") {
            // TODO key stroke exit anyway? (y or n)
            break;
        }
        else {
            std::cout << "Invalid command: \"" << line << "\". Try \"help\""
                      << std::endl;
        }
    }
    return 0;
}

int main(int argc, char *argv[])
{
    std::vector<std::filesystem::path> dbname_paths{"test.db"};

    CLI::App cli{"interactive_db_cli"};
    cli.add_option(
        "--db",
        dbname_paths,
        "A comma-separated list of previously created database paths");
    cli.parse(argc, argv);

    ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = dbname_paths};

    Db ro_db{ro_config};

    std::cout << "Opening read only database ";
    for (auto const &dbname : dbname_paths) {
        std::cout << " " << dbname;
    }
    std::cout << "." << std::endl;

    return interactive_impl(ro_db);
}
