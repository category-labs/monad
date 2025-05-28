#include <gtest/gtest.h>

#include <monad/core/scope_polyfill.hpp>
#include <monad/core/start_lifetime_as_polyfill.hpp>
#include <monad/io/lightweight_binary_logger.h>
#include <monad/util/temp_files.h>
#include <monad/util/ticks_count.h>

#include <chrono>
#include <filesystem>
#include <iostream>

#include <zstd.h>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

TEST(LightWeightBinaryLogger, works)
{
    char path[PATH_MAX]{};
    int const fd = monad_make_temporary_file(path, sizeof(path));
    auto unpath = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(path); });
    uint32_t ops = 0;
    std::chrono::system_clock::time_point when_closed;
    {
        monad_lbl logger;
        to_result(monad_lbl_create(&logger, path, nullptr, 0)).value();
        auto unlogger = monad::make_scope_exit(
            [&]() noexcept { to_result(monad_lbl_destroy(logger)).value(); });
        auto const begin = std::chrono::steady_clock::now();
        for (auto prev = begin, now = begin;;) {
            prev = now;
            now = std::chrono::steady_clock::now();
            if (std::chrono::duration_cast<std::chrono::seconds>(
                    prev - begin) !=
                std::chrono::duration_cast<std::chrono::seconds>(now - begin)) {
                std::cout << "   Ops/sec: "
                          << (1000000ULL * ops /
                              (uint64_t)std::chrono::duration_cast<
                                  std::chrono::microseconds>(now - begin)
                                  .count())
                          << std::endl;
            }
            for (size_t n = 0; n < 1024; n++) {
                to_result(
                    monad_lbl_add(
                        logger, (char const *)&ops, (uint32_t)sizeof(ops)))
                    .value();
                ops++;
            }
            if (now - begin > std::chrono::seconds(10)) {
                break;
            }
        }
        when_closed = std::chrono::system_clock::now();
        to_result(monad_lbl_flush(logger)).value();
        auto const end = std::chrono::steady_clock::now();
        std::cout << "\n   Average ops/sec: "
                  << (1000000LL * ops /
                      std::chrono::duration_cast<std::chrono::microseconds>(
                          end - begin)
                          .count())
                  << " log entries written " << ops << std::endl;
        std::cout << "   Total uncompressed bytes written "
                  << logger->uncompressed_bytes_written
                  << " file bytes written " << logger->file_bytes_written
                  << " which is a compression ratio of "
                  << (100ULL * logger->file_bytes_written /
                      logger->uncompressed_bytes_written)
                  << "%" << std::endl;
        std::cout << "   There were " << logger->write_buffer_starvation_events
                  << " write buffer starvation events and "
                  << logger->pacing_events << " pacing events." << std::endl;
        auto const length = std::filesystem::file_size(path);
        std::cout << "\n   Log file written length is " << length << std::endl;
        EXPECT_EQ(
            logger->uncompressed_bytes_written,
            sizeof(monad_lbl_file_header) +
                (size_t)ops *
                    (sizeof(monad_lbl_entry_header) + sizeof(uint32_t)));
        EXPECT_EQ(length, logger->file_bytes_written);
    }

    std::vector<std::byte> buff(std::filesystem::file_size(path));
    ASSERT_EQ(buff.size(), ::read(fd, buff.data(), buff.size()));
    monad_lbl_file_header header{};
    monad_lbl_file_footer footer{};
    auto const now = std::chrono::system_clock::now();
    auto const epoch = now - now.time_since_epoch();
    auto ts_created = epoch;
    std::vector<std::byte> decompressed(2 * 1024 * 1024);
    std::byte *p = buff.data();
    uint32_t count = 0, remainder = 0;
    uint64_t last_timestamp = 0;
    bool first_loop = true;
    while (p < buff.data() + buff.size()) {
        auto const this_segment = *monad::start_lifetime_as<uint32_t>(p);
        auto const written = ZSTD_decompress(
            decompressed.data(), decompressed.size(), p + 4, this_segment - 4);
        MONAD_ASSERT(!ZSTD_isError(written));
        p += this_segment;
        auto *entry = monad::start_lifetime_as<monad_lbl_entry_header>(
            decompressed.data() + remainder);
        if (first_loop) {
            memcpy(&header, decompressed.data(), sizeof(header));
            EXPECT_EQ(0, memcmp(header.magic, "MNL0", 4));
            EXPECT_EQ(header.user_supplied_header_bytes, 0);
            ts_created +=
                std::chrono::nanoseconds(header.utc_ns_count_on_creation);
            std::cout << std::format("\n\n   Log was created on {}", ts_created)
                      << std::endl;
            entry = monad::start_lifetime_as<monad_lbl_entry_header>(
                decompressed.data() + sizeof(header));
            first_loop = false;
        }
        // std::cout << "   This compressed segment is " << this_segment
        //           << " count = " << count << " remainder " << remainder
        //           << std::endl;
        for (; (size_t)(((std::byte *)entry) - decompressed.data()) < written;
             entry = monad::start_lifetime_as<monad_lbl_entry_header>(
                 ((std::byte *)entry) + sizeof(monad_lbl_entry_header) +
                 sizeof(uint32_t))) {
            remainder = (uint32_t)(written - (size_t)(((std::byte *)entry) -
                                                      decompressed.data()));
            if (remainder >=
                sizeof(monad_lbl_entry_header) + sizeof(uint32_t)) {
                if (entry->length == sizeof(footer)) {
                    memcpy(&footer, entry, sizeof(footer));
                    EXPECT_EQ(0, memcmp(footer.magic, "MNL0", 4));
                    auto const ns_elapsed =
                        (1000000000.0 * double(last_timestamp) /
                         double(monad_ticks_per_second()));
                    std::cout << "   Log last entry was "
                              << (ns_elapsed / 1000000000.0)
                              << " secs after log creation." << std::endl;
                    auto const ts_closed =
                        epoch +
                        std::chrono::nanoseconds(footer.utc_ns_count_on_close);
                    auto const ts_ended(
                        ts_created +
                        std::chrono::nanoseconds((long int)ns_elapsed));
                    std::cout << std::format(
                                     "   Therefore estimated log closure on {} "
                                     "was actually {} and log footer says {}. "
                                     "There are {} cpu ticks per second.",
                                     ts_ended,
                                     when_closed,
                                     ts_closed,
                                     monad_ticks_per_second())
                              << std::endl;
                    EXPECT_GT(
                        ts_closed,
                        ts_created + std::chrono::milliseconds(9500));
                    EXPECT_GT(
                        ts_ended, ts_created + std::chrono::milliseconds(9500));
                    EXPECT_GT(
                        ts_ended, when_closed - std::chrono::milliseconds(500));
                    auto const diff1 = double(
                        footer.utc_ns_count_on_close -
                        header.utc_ns_count_on_creation);
                    auto const diff2 = 1000000000.0 *
                                       double(
                                           footer.cpu_ticks_on_close -
                                           header.cpu_ticks_on_creation) /
                                       double(monad_ticks_per_second());
                    std::cout << "   Clock skew was found to be "
                              << (diff2 / diff1) << std::endl;
                    break;
                }
                else {
                    ASSERT_EQ(
                        entry->length,
                        sizeof(monad_lbl_entry_header) + sizeof(uint32_t));
                    ASSERT_EQ(
                        *monad::start_lifetime_as<uint32_t>(entry->content),
                        count);
                    last_timestamp += entry->cpu_ticks_delta;
                    count++;
                }
                remainder = 0;
            }
            else if (remainder > 0) {
                remainder = sizeof(monad_lbl_entry_header) + sizeof(uint32_t) -
                            remainder;
                count++;
            }
        }
    }
    EXPECT_EQ(count, ops);
}
