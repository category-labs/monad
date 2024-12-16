#include <monad/core/bytes.hpp>
#include <monad/event/append_only_log_emitter.hpp>
#include <monad/event/execution_event.h>
#include <monad/event/replay_event_emitter.hpp>

#include <evmc/evmc.hpp>
#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <limits>
#include <stdlib.h>
#include <unistd.h>

using namespace monad;

namespace
{
    std::string to_hex(uint64_t val)
    {
        bytes32_t as_bytes{val};
        byte_string_view view{as_bytes};
        return evmc::hex(view);
    }
}

class EventEmitterFixture : public ::testing::Test
{
protected:
    std::ifstream is;
    std::ofstream os;
    std::filesystem::path temppath;

    void append_event(monad_execution_event_type const kind, bytes32_t const id)
    {
        monad_execution_event const e{.kind = kind, .id = id};
        os.write(
            reinterpret_cast<char const *>(&e), sizeof(monad_execution_event));
        os.flush();
    }

    void SetUp() override
    {
        char temppath2[] = "monad_test_fixture_XXXXXX";
        int const fd = mkstemp(temppath2);
        MONAD_ASSERT(fd != -1);
        ::close(fd);

        temppath = temppath2;
        os.open(temppath, std::ios::binary);

        MONAD_ASSERT(os);
    }

    void TearDown() override
    {
        os.close();
        std::filesystem::remove(temppath);
    }
};

TEST_F(EventEmitterFixture, open_empty)
{
    AppendOnlyLogEmitter emitter(temppath);
    EXPECT_EQ(emitter.next_event(), std::nullopt);

    append_event(MONAD_PROPOSE_BLOCK, bytes32_t{1});

    auto const output_e = emitter.next_event();
    ASSERT_TRUE(output_e.has_value());
    EXPECT_EQ(output_e.value().kind, MONAD_PROPOSE_BLOCK);
    EXPECT_EQ(output_e.value().filename, to_hex(1));
}

TEST_F(EventEmitterFixture, replay_from_start)
{
    append_event(MONAD_PROPOSE_BLOCK, bytes32_t{1});
    append_event(MONAD_FINALIZE_BLOCK, bytes32_t{1});
    append_event(MONAD_VERIFY_BLOCK, bytes32_t{1});

    AppendOnlyLogEmitter emitter(temppath);

    auto const output_e0 = emitter.next_event();
    ASSERT_TRUE(output_e0.has_value());
    EXPECT_EQ(output_e0.value().kind, MONAD_PROPOSE_BLOCK);
    EXPECT_EQ(output_e0.value().filename, to_hex(1));

    auto const output_e1 = emitter.next_event();
    ASSERT_TRUE(output_e1.has_value());
    EXPECT_EQ(output_e1.value().kind, MONAD_FINALIZE_BLOCK);
    EXPECT_EQ(output_e1.value().filename, to_hex(1));

    auto const output_e2 = emitter.next_event();
    ASSERT_TRUE(output_e2.has_value());
    EXPECT_EQ(output_e2.value().kind, MONAD_VERIFY_BLOCK);
    EXPECT_EQ(output_e2.value().filename, to_hex(1));

    // execution is now ahead
    EXPECT_FALSE(emitter.next_event().has_value());
}

TEST_F(EventEmitterFixture, rewind)
{
    for (uint64_t i = 0; i < 6; ++i) {
        append_event(MONAD_PROPOSE_BLOCK, bytes32_t{i});
    }

    monad_execution_event const rewind_e{
        .kind = MONAD_PROPOSE_BLOCK, .id = bytes32_t{3}};
    AppendOnlyLogEmitter emitter(temppath);
    ASSERT_TRUE(emitter.rewind_to_event(rewind_e));

    for (uint64_t i = 3; i < 6; ++i) {
        auto const output_e = emitter.next_event();
        ASSERT_TRUE(output_e.has_value());
        EXPECT_EQ(output_e.value().kind, MONAD_PROPOSE_BLOCK);
        EXPECT_EQ(output_e.value().filename, to_hex(i));
    }
}

TEST_F(EventEmitterFixture, open_bad_data)
{
    uint64_t const garbage = std::numeric_limits<uint64_t>::max();
    os.write(reinterpret_cast<char const *>(&garbage), sizeof(garbage));
    os.flush();

    AppendOnlyLogEmitter emitter(temppath);
    EXPECT_FALSE(emitter.next_event().has_value());

    // simulate consensus writing over the bad data with a proper event
    os.seekp(0, std::ios::beg);
    append_event(MONAD_PROPOSE_BLOCK, bytes32_t{1});

    auto const output_e = emitter.next_event();
    ASSERT_TRUE(output_e.has_value());
    EXPECT_EQ(output_e.value().kind, MONAD_PROPOSE_BLOCK);
    EXPECT_EQ(output_e.value().filename, to_hex(1));
}

TEST_F(EventEmitterFixture, partial_write)
{
    AppendOnlyLogEmitter emitter(temppath);
    ASSERT_FALSE(emitter.next_event().has_value());

    monad_execution_event e{.kind = MONAD_PROPOSE_BLOCK, .id = bytes32_t{1}};
    auto const partial_size = sizeof(monad_execution_event) - 3;

    // write half
    os.write(reinterpret_cast<char *>(&e), partial_size);
    os.flush();

    // no event yet...
    EXPECT_FALSE(emitter.next_event().has_value());

    // write other half
    os.write(reinterpret_cast<char *>(&e) + partial_size, 3);
    os.flush();

    ASSERT_EQ(os.tellp(), sizeof(monad_execution_event));

    auto const output_e = emitter.next_event();
    ASSERT_TRUE(output_e.has_value());
    EXPECT_EQ(output_e.value().kind, MONAD_PROPOSE_BLOCK);
    EXPECT_EQ(output_e.value().filename, to_hex(1));
}

TEST(EventEmitter, replay_emulate)
{
    ReplayEventEmitter emitter;
    EventEmitter::Event ev;

    ev = emitter.next_event().value();
    EXPECT_EQ(ev.kind, MONAD_PROPOSE_BLOCK);
    EXPECT_EQ(ev.filename, "1");
    ev = emitter.next_event().value();
    EXPECT_EQ(ev.kind, MONAD_FINALIZE_BLOCK);
    EXPECT_EQ(ev.filename, "1");
    ev = emitter.next_event().value();
    EXPECT_EQ(ev.kind, MONAD_VERIFY_BLOCK);
    EXPECT_EQ(ev.filename, "1");

    ev = emitter.next_event().value();
    EXPECT_EQ(ev.kind, MONAD_PROPOSE_BLOCK);
    EXPECT_EQ(ev.filename, "2");
    ev = emitter.next_event().value();
    EXPECT_EQ(ev.kind, MONAD_FINALIZE_BLOCK);
    EXPECT_EQ(ev.filename, "2");
    ev = emitter.next_event().value();
    EXPECT_EQ(ev.kind, MONAD_VERIFY_BLOCK);
    EXPECT_EQ(ev.filename, "2");
}
