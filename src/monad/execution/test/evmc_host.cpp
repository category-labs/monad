#include <monad/execution/config.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/precompiles.hpp>

#include <monad/execution/test/fakes.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace execution;

using traits_t = fake::traits::alpha<fake::State::ChangeSet>;

template <concepts::fork_traits<fake::State::ChangeSet> TTraits>
using traits_templated_evmc_host_t = EvmcHost<
    fake::State::ChangeSet, TTraits,
    fake::Evm<
        fake::State::ChangeSet, TTraits,
        fake::static_precompiles::OneHundredGas, fake::Interpreter>>;

using evmc_host_t = traits_templated_evmc_host_t<traits_t>;

bool operator==(evmc_tx_context const &lhs, evmc_tx_context const &rhs)
{
    return !std::memcmp(
               lhs.tx_gas_price.bytes,
               rhs.tx_gas_price.bytes,
               sizeof(evmc_bytes32)) &&
           !std::memcmp(
               lhs.tx_origin.bytes,
               rhs.tx_origin.bytes,
               sizeof(evmc_address)) &&
           !std::memcmp(
               lhs.block_coinbase.bytes,
               rhs.block_coinbase.bytes,
               sizeof(evmc_address)) &&
           lhs.block_number == rhs.block_number &&
           lhs.block_timestamp == rhs.block_timestamp &&
           lhs.block_gas_limit == rhs.block_gas_limit &&
           !std::memcmp(
               lhs.block_prev_randao.bytes,
               rhs.block_prev_randao.bytes,
               sizeof(evmc_bytes32)) &&
           !std::memcmp(
               lhs.chain_id.bytes, rhs.chain_id.bytes, sizeof(evmc_bytes32)) &&
           !std::memcmp(
               lhs.block_base_fee.bytes,
               rhs.block_base_fee.bytes,
               sizeof(evmc_bytes32));
}

TEST(EvmcHost, get_tx_context)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto bene{
        0xbebebebebebebebebebebebebebebebebebebebe_address};
    BlockHeader b{
        .mix_hash =
            0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32,
        .difficulty = 10'000'000u,
        .number = 15'000'000,
        .gas_limit = 50'000,
        .timestamp = 1677616016,
        .beneficiary = bene,
        .base_fee_per_gas = 37'000'000'000,
    };
    Transaction const t{.sc = {.chain_id = 1}, .from = from};
    fake::State::ChangeSet s{};

    static uint256_t const gas_cost = 37'000'000'000;
    static uint256_t const chain_id{1};
    static uint256_t const base_fee_per_gas{37'000'000'000};

    evmc_host_t host{b, t, s};

    auto const result = host.get_tx_context();
    evmc_tx_context ctx{
        .tx_origin = *t.from,
        .block_coinbase = bene,
        .block_number = 15'000'000,
        .block_timestamp = 1677616016,
        .block_gas_limit = 50'000,
        .block_prev_randao = evmc::uint256be{10'000'000u},
    };
    intx::be::store(ctx.tx_gas_price.bytes, gas_cost);
    intx::be::store(ctx.chain_id.bytes, chain_id);
    intx::be::store(ctx.block_base_fee.bytes, base_fee_per_gas);
    EXPECT_EQ(result, ctx);

    b.difficulty = 0;
    auto const pos_result = host.get_tx_context();
    std::memcpy(
        ctx.block_prev_randao.bytes, b.mix_hash.bytes, sizeof(b.mix_hash));
    EXPECT_EQ(pos_result, ctx);
}

TEST(EvmcHost, emit_log)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto topic0{
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32};
    static constexpr auto topic1{
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32};
    static constexpr bytes32_t topics[] = {topic0, topic1};
    static byte_string const data = {0x00, 0x01, 0x02, 0x03, 0x04};
    BlockHeader const b{};
    Transaction const t{};
    fake::State::ChangeSet s{};

    evmc_host_t host{b, t, s};

    host.emit_log(
        from,
        data.data(),
        data.size(),
        topics,
        sizeof(topics) / sizeof(bytes32_t));

    auto const logs = s.logs();
    EXPECT_EQ(logs.size(), 1);
    EXPECT_EQ(logs[0].address, from);
    EXPECT_EQ(logs[0].data, data);
    EXPECT_EQ(logs[0].topics.size(), 2);
    EXPECT_EQ(logs[0].topics[0], topic0);
    EXPECT_EQ(logs[0].topics[1], topic1);
}
