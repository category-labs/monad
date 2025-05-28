#include <chrono>
#include <gtest/gtest.h>

#include <monad/core/scope_polyfill.hpp>
#include <monad/io/lightweight_binary_logger.h>
#include <monad/io/lightweight_binary_logger_cli_tool_impl.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <thread>

TEST(lbl_cli_tool, no_args_prints_fatal_and_help)
{
    std::stringstream cout;
    std::stringstream cerr;
    std::string_view args[] = {"monad_lbl"};
    int const retcode = main_impl(cout, cerr, args);
    ASSERT_EQ(retcode, 1);
    EXPECT_TRUE(cerr.str().starts_with("FATAL:"));
    EXPECT_NE(std::string::npos, cerr.str().find("Options:"));
}

TEST(lbl_cli_tool, help_prints_help)
{
    std::stringstream cout;
    std::stringstream cerr;
    std::string_view args[] = {"monad_lbl", "--help"};
    int const retcode = main_impl(cout, cerr, args);
    ASSERT_EQ(retcode, 0);
    EXPECT_NE(std::string::npos, cout.str().find("Options:"));
}

TEST(lbl_cli_tool, generic_works)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    auto const fd = mkstemp(temppath);
    if (-1 == fd) {
        abort();
    }
    ::close(fd);
    auto untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });
    std::cout << "temp file being used: " << temppath << std::endl;

    monad_lbl logger;
    to_result(monad_lbl_create(&logger, temppath, nullptr, 0)).value();
    auto unlogger = monad::make_scope_exit(
        [&]() noexcept { (void)monad_lbl_destroy(logger); });
    std::chrono::system_clock::time_point ts1;
    for (uint32_t n = 0; n < 256; n++) {
        if (n == 128) {
            std::this_thread::sleep_for(std::chrono::seconds(1));
            ts1 = std::chrono::system_clock::now();
        }
        to_result(monad_lbl_add(logger, &n, 4)).value();
    }
    unlogger.release();
    to_result(monad_lbl_destroy(logger)).value();

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {"monad_lbl", "--file", temppath};
        int const retcode = main_impl(cout, cerr, args);
        ASSERT_EQ(retcode, 0);
        EXPECT_NE(
            std::string::npos, cout.str().find("l = 4 content = ff 00 00 00"));
    }
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {"monad_lbl", "--file", temppath, "--csv"};
        int const retcode = main_impl(cout, cerr, args);
        ASSERT_EQ(retcode, 0);
        EXPECT_NE(std::string::npos, cout.str().find("4,\"ff 00 00 00\""));
    }
    auto strip_prec = [](std::string v) {
        auto const idx = v.rfind('.');
        if (idx != v.npos) {
            v.resize(idx);
            v.push_back('Z');
        }
        return v;
    };
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string from = strip_prec(
            std::format("{:" MONAD_LBL_CLI_TOOL_DATETIME_FORMAT "}", ts1));
        std::string_view args[] = {
            "monad_lbl", "--file", temppath, "--from", from, "--count", "1"};
        int const retcode = main_impl(cout, cerr, args);
        std::cout << "cerr was:\n" << cerr.str() << std::endl;
        std::cout << "cout was:\n" << cout.str() << std::endl;
        ASSERT_EQ(retcode, 0);
        auto s = std::move(cout).str();
        EXPECT_EQ(std::count(s.begin(), s.end(), '\n'), 1);
        EXPECT_NE(std::string::npos, s.find("l = 4 content = 80 00 00 00"));
    }
}

TEST(lbl_cli_tool, db_write_io_works)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    auto const fd = mkstemp(temppath);
    if (-1 == fd) {
        abort();
    }
    ::close(fd);
    auto untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });
    std::cout << "temp file being used: " << temppath << std::endl;

    monad_lbl logger;
    to_result(monad_lbl_create(
                  &logger,
                  temppath,
                  monad_lbl_db_write_io_log,
                  sizeof(monad_lbl_db_write_io_log)))
        .value();
    auto unlogger = monad::make_scope_exit(
        [&]() noexcept { (void)monad_lbl_destroy(logger); });

    class binary_log_entry
    {
    public:
        const enum type_t : uint8_t { read, write, discard } type;

    protected:
        explicit constexpr binary_log_entry(type_t t)
            : type{t}
        {
        }
    };

    static_assert(std::is_trivially_copyable_v<binary_log_entry>);

#pragma pack(push)
#pragma pack(4)

    union read_log_entry
    {
        binary_log_entry erased;

        struct
        {
            uint64_t type : 8;
            uint64_t chunk_id : 20;
            uint64_t chunk_offset : 28;
            uint64_t reserved0_ : 8;
            uint32_t length;
        };

        constexpr read_log_entry(
            uint32_t chunk_id_, uint64_t offset_, uint32_t length_)
        {
            type = binary_log_entry::read;
            chunk_id = chunk_id_ & 0xFFFFF;
            chunk_offset = offset_ & 0xFFFFFFF;
            length = length_;
        }
    };

#pragma pack(pop)

    static_assert(std::is_trivially_copyable_v<read_log_entry>);
    static_assert(sizeof(read_log_entry) == 12);
    static_assert(alignof(read_log_entry) == 4);

#pragma pack(push)
#pragma pack(4)

    union write_log_entry
    {
        binary_log_entry erased;

        struct
        {
            uint64_t type : 8;
            uint64_t chunk_id : 20;
            uint64_t chunk_offset : 28;
            uint64_t reserved0_ : 8;
            uint64_t device_offset;
            uint32_t length;
        };

        constexpr write_log_entry(
            uint32_t chunk_id_, uint64_t chunk_offset_, uint64_t device_offset_,
            uint32_t length_)
        {
            type = binary_log_entry::write;
            chunk_id = chunk_id_ & 0xFFFFF;
            chunk_offset = chunk_offset_ & 0xFFFFFFF;
            device_offset = device_offset_;
            length = length_;
        }
    };

#pragma pack(pop)

    static_assert(std::is_trivially_copyable_v<write_log_entry>);
    static_assert(sizeof(write_log_entry) == 20);
    static_assert(alignof(write_log_entry) == 4);

#pragma pack(push)
#pragma pack(4)

    union discard_log_entry
    {
        binary_log_entry erased;

        struct
        {
            uint64_t type : 8;
            uint64_t chunk_id : 20;
            uint64_t chunk_offset : 28;
            uint64_t reserved0_ : 8;
            uint64_t device_offset;
            uint32_t length;
        };

        constexpr discard_log_entry(
            uint32_t chunk_id_, uint64_t chunk_offset_, uint64_t device_offset_,
            uint32_t length_)
        {
            type = binary_log_entry::write;
            chunk_id = chunk_id_ & 0xFFFFF;
            chunk_offset = chunk_offset_ & 0xFFFFFFF;
            device_offset = device_offset_;
            length = length_;
        }
    };

#pragma pack(pop)

    static_assert(std::is_trivially_copyable_v<discard_log_entry>);
    static_assert(sizeof(discard_log_entry) == 20);
    static_assert(alignof(discard_log_entry) == 4);

    for (uint32_t n = 0; n < 256; n++) {
        std::byte buffer[64];
        size_t towrite = 0;
        switch (n % 3) {
        case 0:
            new (buffer) read_log_entry(n, n, n);
            towrite = sizeof(read_log_entry);
            break;
        case 1:
            new (buffer) write_log_entry(n, n, n, n);
            towrite = sizeof(write_log_entry);
            break;
        case 2:
            new (buffer) discard_log_entry(n, n, n, n);
            towrite = sizeof(discard_log_entry);
            break;
        }
        to_result(monad_lbl_add(logger, buffer, towrite)).value();
    }
    unlogger.release();
    to_result(monad_lbl_destroy(logger)).value();

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {"monad_lbl", "--file", temppath};
        int const retcode = main_impl(cout, cerr, args);
        ASSERT_EQ(retcode, 0);
        EXPECT_NE(
            std::string::npos,
            cout.str().find("read chunk id = 255 offset = 255 bytes = 255"));
    }
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {"monad_lbl", "--file", temppath, "--csv"};
        int const retcode = main_impl(cout, cerr, args);
        ASSERT_EQ(retcode, 0);
        EXPECT_NE(std::string::npos, cout.str().find("read,255,255,255,"));
    }
}
