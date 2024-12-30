#include <monad/rpc/eth_call.hpp>

#include <monad/core/block.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>

#include <gtest/gtest.h>

#include <string>
#include <vector>

using namespace monad;

std::vector<uint8_t> to_vec(byte_string const &bs)
{
    std::vector<uint8_t> v{bs.begin(), bs.end()};
    return v;
}

TEST(eth_call, simple_success_call)
{
    auto const path = [] {
        std::filesystem::path dbname(
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "monad_eth_call_test1_XXXXXX");
        int const fd = ::mkstemp((char *)dbname.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(
            -1 !=
            ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
        ::close(fd);
        return dbname;
    }();

    OnDiskMachine machine;
    mpt::Db db{
        machine, mpt::OnDiskDbConfig{.append = false, .dbname_paths = {path}}};
    TrieDb tdb{db};

    for (uint64_t i = 0; i < 256; ++i) {
        BlockHeader hdr{.number = i};
        tdb.commit({}, {}, hdr, {}, {}, {}, {}, std::nullopt);
    }

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto to{
        0x5353535353535353535353535353535353535353_address};

    Transaction tx{
        .gas_limit = 100000u, .to = to, .type = TransactionType::eip1559};
    BlockHeader header{.number = 256};

    tdb.commit({}, {}, header, {}, {}, {}, {}, std::nullopt);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));

    monad_state_override_set state_override;

    auto const result =
        eth_call(rlp_tx, rlp_header, rlp_sender, 256u, path, state_override);

    EXPECT_TRUE(result.status_code == EVMC_SUCCESS);
}

TEST(eth_call, failed_to_read)
{
    auto const path = [] {
        std::filesystem::path dbname(
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "monad_eth_call_test2_XXXXXX");
        int const fd = ::mkstemp((char *)dbname.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(
            -1 !=
            ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
        ::close(fd);
        return dbname;
    }();

    OnDiskMachine machine;
    mpt::Db db{
        machine, mpt::OnDiskDbConfig{.append = false, .dbname_paths = {path}}};
    TrieDb tdb{db};

    // one block short
    for (uint64_t i = 1; i < 256; ++i) {
        BlockHeader hdr{.number = i};
        tdb.commit({}, {}, hdr, {}, {}, {}, {}, std::nullopt);
    }

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto to{
        0x5353535353535353535353535353535353535353_address};

    Transaction tx{
        .gas_limit = 100000u, .to = to, .type = TransactionType::eip1559};
    BlockHeader header{.number = 256};

    tdb.commit({}, {}, header, {}, {}, {}, {}, std::nullopt);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));

    monad_state_override_set state_override;

    auto const result =
        eth_call(rlp_tx, rlp_header, rlp_sender, 256u, path, state_override);

    EXPECT_TRUE(result.status_code == EVMC_FAILURE);
}
