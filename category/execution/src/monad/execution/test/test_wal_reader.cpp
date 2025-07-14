#include <category/core/blake3.hpp>
#include <category/core/bytes.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/rlp/monad_block_rlp.hpp>
#include <monad/execution/wal_reader.hpp>

#include <evmc/evmc.hpp>
#include <gtest/gtest.h>
#include <test_resource_data.h>

#include <cstdint>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <limits>
#include <stdlib.h>
#include <unistd.h>

using namespace monad;

class WalReaderTestFixture : public ::testing::Test
{
protected:
    std::ofstream wal_os;
    std::filesystem::path ledger_dir;

    bytes32_t write_dummy_block(uint64_t const round)
    {
        MonadConsensusBlockBody body;
        MonadConsensusBlockHeader header;
        header.block_body_id =
            to_bytes(blake3(rlp::encode_consensus_block_body(body)));
        header.round = round;
        auto const encoded_body = rlp::encode_consensus_block_body(body);
        auto const encoded_header = rlp::encode_consensus_block_header(header);
        auto const header_bft_id = to_bytes(blake3(encoded_header));

        std::ofstream header_os{
            ledger_dir / (evmc::hex(header_bft_id) + ".header")};
        std::ofstream body_os{
            ledger_dir / (evmc::hex(header.block_body_id) + ".body")};
        body_os.write(
            reinterpret_cast<char const *>(encoded_body.data()),
            static_cast<std::streamsize>(encoded_body.size()));
        header_os.write(
            reinterpret_cast<char const *>(encoded_header.data()),
            static_cast<std::streamsize>(encoded_header.size()));
        body_os.flush();
        header_os.flush();

        return header_bft_id;
    }

    bytes32_t append_entry(WalAction const action, uint64_t const round)
    {
        auto const header_bft_id = write_dummy_block(round);
        WalEntry const entry{.action = action, .id = header_bft_id};
        wal_os.write(reinterpret_cast<char const *>(&entry), sizeof(WalEntry));
        wal_os.flush();
        return header_bft_id;
    }

    void SetUp() override
    {
        char fixture_template[] = "monad_block_reader_fixture_XXXXXX";
        char *temppath = mkdtemp(fixture_template);
        MONAD_ASSERT(temppath != nullptr);
        ledger_dir = temppath;

        wal_os.open(ledger_dir / "wal", std::ios::binary);

        MONAD_ASSERT(wal_os);
    }

    void TearDown() override
    {
        wal_os.close();
        std::filesystem::remove_all(ledger_dir);
    }
};

TEST_F(WalReaderTestFixture, open_empty)
{
    WalReader reader(ledger_dir);
    EXPECT_EQ(reader.next(), std::nullopt);

    append_entry(WalAction::PROPOSE, 1);

    auto const output_e = reader.next();
    ASSERT_TRUE(output_e.has_value());
    EXPECT_EQ(output_e.value().action, WalAction::PROPOSE);
    EXPECT_EQ(output_e.value().header.round, 1);
}

TEST_F(WalReaderTestFixture, replay_from_start)
{
    append_entry(WalAction::PROPOSE, 1);
    append_entry(WalAction::FINALIZE, 1);

    WalReader reader(ledger_dir);

    auto const a0 = reader.next();
    ASSERT_TRUE(a0.has_value());
    EXPECT_EQ(a0.value().action, WalAction::PROPOSE);
    EXPECT_EQ(a0.value().header.round, 1);

    auto const a1 = reader.next();
    ASSERT_TRUE(a1.has_value());
    EXPECT_EQ(a1.value().action, WalAction::FINALIZE);
    EXPECT_EQ(a1.value().header.round, 1);

    // execution is now ahead
    EXPECT_FALSE(reader.next().has_value());
}

TEST_F(WalReaderTestFixture, rewind)
{
    std::vector<bytes32_t> header_bft_ids;
    for (uint64_t i = 0; i < 6; ++i) {
        header_bft_ids.emplace_back(append_entry(WalAction::PROPOSE, i));
    }

    WalEntry const bad_rewind{
        .action = WalAction::FINALIZE, .id = bytes32_t{70'000}};
    WalEntry const good_rewind{
        .action = WalAction::PROPOSE, .id = header_bft_ids[3]};

    WalReader reader(ledger_dir);
    ASSERT_FALSE(reader.rewind_to(bad_rewind));
    ASSERT_TRUE(reader.rewind_to(good_rewind));

    for (uint64_t i = 3; i < 6; ++i) {
        auto const action = reader.next();
        ASSERT_TRUE(action.has_value());
        EXPECT_EQ(action.value().action, WalAction::PROPOSE);
        EXPECT_EQ(action.value().header.round, i);
    }
}

TEST_F(WalReaderTestFixture, open_bad_data)
{
    uint64_t const garbage = std::numeric_limits<uint64_t>::max();
    wal_os.write(reinterpret_cast<char const *>(&garbage), sizeof(garbage));
    wal_os.flush();

    WalReader reader(ledger_dir);
    EXPECT_FALSE(reader.next().has_value());

    // simulate consensus writing over the bad data with a proper event
    wal_os.seekp(0, std::ios::beg);
    append_entry(WalAction::PROPOSE, 1);

    auto const action = reader.next();
    ASSERT_TRUE(action.has_value());
    EXPECT_EQ(action.value().action, WalAction::PROPOSE);
    EXPECT_EQ(action.value().header.round, 1);
}

TEST_F(WalReaderTestFixture, partial_write)
{
    WalReader reader(ledger_dir);
    ASSERT_FALSE(reader.next().has_value());

    auto const header_bft_id = write_dummy_block(1);
    WalEntry entry{.action = WalAction::PROPOSE, .id = header_bft_id};
    auto const partial_size = sizeof(WalEntry) - 3;

    // write half
    wal_os.write(reinterpret_cast<char *>(&entry), partial_size);
    wal_os.flush();

    // no event yet...
    EXPECT_FALSE(reader.next().has_value());

    // write other half
    wal_os.write(reinterpret_cast<char *>(&entry) + partial_size, 3);
    wal_os.flush();
    ASSERT_EQ(wal_os.tellp(), sizeof(WalEntry));

    auto const next_action = reader.next();
    ASSERT_TRUE(next_action.has_value());
    EXPECT_EQ(next_action.value().action, WalAction::PROPOSE);
    EXPECT_EQ(next_action.value().header.round, 1);
}
