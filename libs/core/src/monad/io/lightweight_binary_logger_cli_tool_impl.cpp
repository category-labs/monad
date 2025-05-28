#include <CLI/CLI.hpp>

#include "lightweight_binary_logger_cli_tool_impl.hpp"

#include "lightweight_binary_logger.h"

#include <monad/core/assert.h>
#include <monad/core/scope_polyfill.hpp>
#include <monad/core/start_lifetime_as_polyfill.hpp>
#include <monad/util/ticks_count.h>

// Can't be <monad/ prefixed as we can't link to this library
#include "../../async/src/monad/async/storage_pool.hpp"

#include <chrono>
#include <ctime>
#include <filesystem>
#include <format>
#include <fstream>
#include <iostream>
#include <span>
#include <sstream>
#include <system_error>
#include <vector>

#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <zstd.h>

struct impl_t
{
    std::ostream &cout;
    std::ostream &cerr;
    std::filesystem::path path, output;
    bool output_csv{false};
    std::string from_str, until_str;
    std::chrono::system_clock::time_point from, until;
    uint32_t count{UINT32_MAX};

    std::chrono::system_clock::time_point epoch;
    std::span<std::byte const> mapped_file;
    std::optional<std::ofstream> out;
    bool first_run{false};

    struct chunk_info_t
    {
        std::span<std::byte const> mapped_file;
        std::vector<std::byte> decompressed;
        monad_lbl_entry_header const *first_entry{nullptr};

        chunk_info_t(std::byte const *p, size_t bytes)
            : mapped_file(p, bytes)
        {
        }

        void decompress()
        {
            if (decompressed.empty()) {
                auto const shall_decompress_bytes = ZSTD_getFrameContentSize(
                    mapped_file.data(), mapped_file.size());
                MONAD_ASSERT(!ZSTD_isError(shall_decompress_bytes));
                decompressed.resize(shall_decompress_bytes);
                auto const written = ZSTD_decompress(
                    decompressed.data(),
                    decompressed.size(),
                    mapped_file.data(),
                    mapped_file.size());
                MONAD_ASSERT(!ZSTD_isError(written));
                decompressed.resize(written);
                first_entry = monad::start_lifetime_as<monad_lbl_entry_header>(
                    decompressed.data());
            }
        }

        void clear()
        {
            decompressed.clear();
            decompressed.shrink_to_fit();
        }
    };

    std::vector<chunk_info_t> chunks;
    monad_lbl_file_header const *file_header{nullptr};
    std::optional<monad_lbl_file_footer> file_footer;
    double clock_skew{1.0}; // multiplier for entry datestamps

public:
    impl_t(std::ostream &cout_, std::ostream &cerr_)
        : cout(cout_)
        , cerr(cerr_)
    {
        auto const now = std::chrono::system_clock::now();
        epoch = now - now.time_since_epoch();
        from = epoch;
        until = from + std::chrono::nanoseconds(INT64_MAX);
    }

    ~impl_t()
    {
        if (!mapped_file.empty()) {
            (void)::munmap((void *)mapped_file.data(), mapped_file.size());
            mapped_file = {};
        }
    }

    void load()
    {
        if (mapped_file.empty()) {
            int fd = ::open(path.c_str(), O_RDONLY | O_CLOEXEC);
            if (-1 == fd) {
                throw std::system_error(
                    std::error_code(errno, std::system_category()));
            }
            auto unfd =
                monad::make_scope_exit([&]() noexcept { (void)::close(fd); });
            struct stat s = {};
            if (-1 == ::fstat(fd, &s)) {
                throw std::system_error(
                    std::error_code(errno, std::system_category()));
            }
            void *p =
                mmap(nullptr, (size_t)s.st_size, PROT_READ, MAP_SHARED, fd, 0);
            if (p == MAP_FAILED) {
                throw std::system_error(
                    std::error_code(errno, std::system_category()));
            }
            mapped_file = {(std::byte *)p, (size_t)s.st_size};
        }
        if (!output.empty()) {
            out = std::ofstream(
                output, std::ios::out | std::ios::app | std::ios::trunc);
            out->exceptions(std::ofstream::failbit | std::ofstream::badbit);
        }
        chunks.clear();
        for (auto const *p = mapped_file.data();
             p < mapped_file.data() + mapped_file.size();) {
            uint32_t const thischunk = *monad::start_lifetime_as<uint32_t>(p);
            chunks.emplace_back(p + 4, thischunk - 4);
            p += thischunk;
        }
        file_header = nullptr;
        file_footer.reset();
        clock_skew = 1.0;
        if (!chunks.empty()) {
            chunks.front().decompress();
            file_header = monad::start_lifetime_as<monad_lbl_file_header>(
                chunks.front().decompressed.data());
            MONAD_ASSERT(0 == memcmp(file_header->magic, "MNL0", 4));
            chunks.front().first_entry =
                monad::start_lifetime_as<monad_lbl_entry_header>(
                    chunks.front().decompressed.data() +
                    sizeof(monad_lbl_file_header) +
                    file_header->user_supplied_header_bytes);

            chunks.back().decompress();
            auto const *p = chunks.back().decompressed.data() +
                            chunks.back().decompressed.size();
            p -= sizeof(monad_lbl_file_footer);
            auto const *f = monad::start_lifetime_as<monad_lbl_file_footer>(p);
            if (0 == memcmp(f->magic, "MNL0", 4)) {
                file_footer.emplace(*f);
                chunks.back().decompressed.resize(
                    chunks.back().decompressed.size() -
                    sizeof(monad_lbl_file_footer));
                auto const ticks_diff =
                    1000000000.0 *
                    double(
                        file_footer->cpu_ticks_on_close -
                        file_header->cpu_ticks_on_creation) /
                    double(monad_ticks_per_second());
                auto const utc_diff = double(
                    file_footer->utc_ns_count_on_close -
                    file_header->utc_ns_count_on_creation);
                clock_skew = utc_diff / ticks_diff;
                auto const creation_ts =
                    epoch + std::chrono::nanoseconds(
                                file_header->utc_ns_count_on_creation);
                auto const closed_ts =
                    epoch + std::chrono::nanoseconds(
                                file_footer->utc_ns_count_on_close);
                cerr << std::format(
                            "Log file was created on "
                            "{:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT
                            "} and closed on "
                            "{:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT "}. Clock "
                            "skew was calculated as {}",
                            creation_ts,
                            closed_ts,
                            clock_skew)
                     << std::endl;
            }
            else {
                auto const creation_ts =
                    epoch + std::chrono::nanoseconds(
                                file_header->utc_ns_count_on_creation);
                cerr << std::format(
                            "WARNING: Log file end was truncated! Assuming "
                            "clock skew was 1.0. Log file was created on "
                            "{:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT "}",
                            creation_ts)
                     << std::endl;
            }
        }
    }

    void output_log_entry_generic(
        std::chrono::system_clock::time_point ts,
        monad_lbl_entry_header const *entry)
    {
        auto &ss = out ? (std::ostream &)*out : cout;
        if (output_csv && first_run) {
            ss << R"(Timestamp,"Content Length","First eight bytes"
)";
            first_run = false;
        }
        static std::string bytesstr;
        bytesstr.clear();
        bytesstr.resize(16 * 3);
        char *p = bytesstr.data();
        auto const length = entry->length - sizeof(monad_lbl_entry_header);
        for (size_t n = 0; n < length && n < 8; n++) {
            auto const res = std::to_chars(
                p,
                bytesstr.data() + bytesstr.size(),
                (uint8_t)entry->content[n],
                16);
            if (res.ec != std::errc{}) {
                throw std::system_error(std::make_error_code(res.ec));
            }
            if (res.ptr == p + 1) {
                *++p = res.ptr[-1];
                res.ptr[-1] = '0';
                p++;
            }
            else {
                p += 2;
            }
            *p++ = ' ';
        }
        bytesstr.resize(size_t(p - bytesstr.data()));
        if (!bytesstr.empty()) {
            bytesstr.resize(bytesstr.size() - 1);
        }
        if (output_csv) {
            ss << std::format(
                "\"{:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT "}\",{},\"{}\"\n",
                ts,
                length,
                bytesstr);
        }
        else {
            char const *ellipsis = (length > 8) ? "..." : "";
            ss << std::format(
                "{:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT
                "}: l = {} content = {} {}\n",
                ts,
                length,
                bytesstr,
                ellipsis);
        }
    }

    void output_log_entry_db_write_io(
        std::chrono::system_clock::time_point ts,
        monad_lbl_entry_header const *entry)
    {
        auto &ss = out ? (std::ostream &)*out : cout;
        if (output_csv && first_run) {
            ss << R"(Timestamp,Operation,"Chunk Id",Offset,Bytes,"Device Offset"
)";
            first_run = false;
        }
        MONAD_ASSERT(entry->length > sizeof(monad_lbl_entry_header));
        auto const *p = monad::start_lifetime_as<
            monad::async::storage_pool::binary_log_entry>(entry->content);
        switch (p->type) {
        case monad::async::storage_pool::binary_log_entry::read: {
            auto const *p2 = monad::start_lifetime_as<
                monad::async::storage_pool::read_log_entry>(entry->content);
            if (output_csv) {
                ss << std::format(
                    "\"{:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT
                    "}\",read,{},{},{},\n",
                    ts,
                    p2->chunk_id,
                    p2->chunk_offset,
                    p2->length);
            }
            else {
                ss << std::format(
                    "{:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT
                    "}: read chunk id = {} offset = {} bytes = {}\n",
                    ts,
                    p2->chunk_id,
                    p2->chunk_offset,
                    p2->length);
            }
            break;
        }
        case monad::async::storage_pool::binary_log_entry::write: {
            auto const *p2 = monad::start_lifetime_as<
                monad::async::storage_pool::write_log_entry>(entry->content);
            if (output_csv) {
                ss << std::format(
                    "\"{:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT
                    "}\",write,{},{},{},{}\n",
                    ts,
                    p2->chunk_id,
                    p2->chunk_offset,
                    p2->length,
                    p2->device_offset);
            }
            else {
                ss << std::format(
                    "{:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT
                    "}: write chunk id = {} offset = {} bytes = {} device "
                    "offset "
                    "= {}\n",
                    ts,
                    p2->chunk_id,
                    p2->chunk_offset,
                    p2->length,
                    p2->device_offset);
            }
            break;
        }
        case monad::async::storage_pool::binary_log_entry::discard: {
            auto const *p2 = monad::start_lifetime_as<
                monad::async::storage_pool::discard_log_entry>(entry->content);
            if (output_csv) {
                ss << std::format(
                    "\"{:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT
                    "}\",discard,{},{},{},{}\n",
                    ts,
                    p2->chunk_id,
                    p2->chunk_offset,
                    p2->length,
                    p2->device_offset);
            }
            else {
                ss << std::format(
                    "{:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT
                    "}: discard chunk id = {} offset = {} bytes = {} device "
                    "offset = {}\n",
                    ts,
                    p2->chunk_id,
                    p2->chunk_offset,
                    p2->length,
                    p2->device_offset);
            }
            break;
        }
        default:
            return output_log_entry_generic(ts, entry);
        }
    }

    void run()
    {
        first_run = true;
        auto const output_log_entry_func = [this] {
            if (file_header->user_supplied_header_bytes < 8) {
                return &impl_t::output_log_entry_generic;
            }
            if (0 == memcmp(
                         file_header->user_supplied_header,
                         monad_lbl_db_write_io_log,
                         sizeof(monad_lbl_db_write_io_log))) {
                return &impl_t::output_log_entry_db_write_io;
            }
            return &impl_t::output_log_entry_generic;
        }();
        if (from != epoch ||
            until != from + std::chrono::nanoseconds(INT64_MAX)) {
            cerr << std::format(
                        "NOTE: Only showing log entries between "
                        "{:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT
                        "} and {:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT "}",
                        from,
                        until)
                 << std::endl;
        }
        auto const creation_ts =
            epoch +
            std::chrono::nanoseconds(file_header->utc_ns_count_on_creation);
        uint64_t tick_count = 0;
        uint32_t log_entries_output = 0;
        auto const ticks_per_second =
            1000000000.0 / double(monad_ticks_per_second());
        for (auto &chunk : chunks) {
            chunk.decompress();
            for (auto const *entry = chunk.first_entry;
                 (std::byte *)entry <
                 chunk.decompressed.data() + chunk.decompressed.size();
                 entry = (monad_lbl_entry_header *)((std::byte *)entry +
                                                    entry->length)) {
                tick_count += entry->cpu_ticks_delta;
                auto const ts =
                    creation_ts + std::chrono::nanoseconds(
                                      (int64_t)(double(tick_count) *
                                                ticks_per_second * clock_skew));
                if (ts >= from && ts < until) {
                    (this->*output_log_entry_func)(ts, entry);
                    log_entries_output++;
                    if (log_entries_output >= count) {
                        return;
                    }
                }
            }
            chunk.clear();
        }
    }
};

int main_impl(
    std::ostream &cout, std::ostream &cerr, std::span<std::string_view> args)
{
    CLI::App cli(
        "Tool for parsing LBL files (lightweight binary logger)", "monad_lbl");
    try {
        impl_t impl(cout, cerr);
        cli.add_option("--file", impl.path, "path to the LBL file.")
            ->required();
        cli.add_option(
            "--output",
            impl.output,
            "write log entries to this file instead of to stdout.");
        cli.add_flag(
            "--csv",
            impl.output_csv,
            "write log entries in comma separated values format.");
        cli.add_option(
            "--from", impl.from_str, "do not show log entries before this.");
        cli.add_option(
            "--until", impl.until_str, "do not show log entries after this.");
        cli.add_option(
            "--count", impl.count, "show this many log entries in total.");
        {
            // Weirdly CLI11 wants reversed args for its vector consuming
            // overload
            std::vector<std::string> rargs(args.rbegin(), --args.rend());
            cli.parse(std::move(rargs));
        }
        // C++ 20 std::chrono::parse() is still not implemented ... sigh
        auto parse =
            [](std::string const &s) -> std::chrono::system_clock::time_point {
            std::tm tm = {};
            std::stringstream ss(s);
            ss >> std::get_time(&tm, MONAD_LBL_CLI_TOOL_DATETIME_FORMAT);
            if (ss.bad() || ss.fail()) {
                throw std::runtime_error(std::format(
                    "Datetime string '{}' does not match format "
                    "'" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT "'",
                    s));
            }
            time_t const secs = timegm(&tm);
            return std::chrono::system_clock::from_time_t(secs);
        };
        if (!impl.from_str.empty()) {
            impl.from = parse(impl.from_str);
        }
        if (!impl.until_str.empty()) {
            impl.until = parse(impl.until_str);
        }
        impl.load();
        impl.run();
    }

    catch (const CLI::CallForHelp &e) {
        cout << cli.help() << std::flush;
    }

    catch (const CLI::RequiredError &e) {
        cerr << "FATAL: " << e.what() << "\n\n";
        cerr << cli.help() << std::flush;
        return 1;
    }

    catch (std::exception const &e) {
        cerr << "FATAL: " << e.what() << std::endl;
        return 1;
    }

    return 0;
}
