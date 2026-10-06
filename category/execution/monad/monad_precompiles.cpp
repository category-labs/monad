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

#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/monad/monad_precompiles.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_contract.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/graph_eval/graph_eval.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <array>
#include <chrono>
#include <cstdint>
#include <format>
#include <iostream>

#include <linux/perf_event.h>
#include <sys/resource.h>
#include <sys/syscall.h>
#include <unistd.h>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// Benchmarking: the calling thread's hardware counters, kernel time included,
// read as one group around each precompile call
class PerfCounters
{
    static constexpr size_t N = 5;
    int leader_ = -1;

public:
    static constexpr char const *names[N] = {
        "cycles", "instructions", "LLC misses", "L1d misses", "L1i misses"};

    PerfCounters()
    {
        constexpr uint64_t read_miss = (PERF_COUNT_HW_CACHE_OP_READ << 8) |
                                       (PERF_COUNT_HW_CACHE_RESULT_MISS << 16);
        std::array<std::pair<uint32_t, uint64_t>, N> const events{{
            {PERF_TYPE_HARDWARE, PERF_COUNT_HW_CPU_CYCLES},
            {PERF_TYPE_HARDWARE, PERF_COUNT_HW_INSTRUCTIONS},
            {PERF_TYPE_HARDWARE, PERF_COUNT_HW_CACHE_MISSES},
            {PERF_TYPE_HW_CACHE, PERF_COUNT_HW_CACHE_L1D | read_miss},
            {PERF_TYPE_HW_CACHE, PERF_COUNT_HW_CACHE_L1I | read_miss},
        }};
        for (auto const &[type, config] : events) {
            perf_event_attr attr{};
            attr.size = sizeof(attr);
            attr.type = type;
            attr.config = config;
            attr.read_format = PERF_FORMAT_GROUP;
            int const fd = static_cast<int>(
                syscall(SYS_perf_event_open, &attr, 0, -1, leader_, 0));
            if (leader_ == -1) {
                leader_ = fd;
            }
        }
    }

    // Zeros for any counter that couldn't be opened
    std::array<uint64_t, N> read() const
    {
        struct
        {
            uint64_t n;
            std::array<uint64_t, N> values;
        } data{};
        if (leader_ < 0 || ::read(leader_, &data, sizeof(data)) < 0) {
            return {};
        }
        return data.values;
    }
};

// Benchmarking: set to count the page faults during each precompile call
constexpr bool COLLECT_PAGE_FAULTS = false;

// Benchmarking: the calling thread's minor and major page faults so far
/*
std::array<uint64_t, 2> page_faults()
{
    rusage usage{};
    getrusage(RUSAGE_THREAD, &usage);
    return {
        static_cast<uint64_t>(usage.ru_minflt),
        static_cast<uint64_t>(usage.ru_majflt)};
}
*/

template <Traits traits, typename Contract, Address contract_address>
std::optional<evmc::Result> check_call_monad_precompile(
    State &state, CallTracerBase &call_tracer, evmc_message const &msg)
{
    auto const start = std::chrono::high_resolution_clock::now();

    if (msg.code_address != contract_address) {
        return std::nullopt;
    }

    if (MONAD_UNLIKELY(msg.kind != EVMC_CALL) || (msg.flags != 0)) {
        return evmc::Result{evmc_status_code::EVMC_REJECTED};
    }

    byte_string_view input{msg.input_data, msg.input_size};
    auto const [method, cost] =
        Contract::template precompile_dispatch<traits>(input);
    if (MONAD_UNLIKELY(std::cmp_less(msg.gas, cost))) {
        return evmc::Result{evmc_status_code::EVMC_OUT_OF_GAS};
    }

    Contract contract = Contract{state, call_tracer};
    auto const res = (contract.*method)(input, msg.sender, msg.value);
    if (MONAD_LIKELY(res.has_value())) {
        int64_t const gas_left = msg.gas - static_cast<int64_t>(cost);
        int64_t const gas_refund = 0;
        auto const end = std::chrono::high_resolution_clock::now();
        // evmc::Result copies the output into memory of its own
        evmc::Result result(
            EVMC_SUCCESS,
            gas_left,
            gas_refund,
            res.value().data(),
            res.value().size());
        auto const copy_end = std::chrono::high_resolution_clock::now();
        std::cout << "Precompile took " << std::chrono::duration_cast<std::chrono::microseconds>(end - start) << "\n";
        std::cout << "  copy output to evmc::Result: "
                  << std::chrono::duration_cast<std::chrono::microseconds>(
                         copy_end - end)
                  << "\n";
        return result;
    }
    return evmc::Result(
        EVMC_REVERT,
        0 /* gas left */,
        0 /* gas refund */,
        reinterpret_cast<uint8_t const *>(res.error().message().data()),
        res.error().message().size());
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <Traits traits>
bool is_precompile(Address const &address)
{
    // Note that if new Monad-specific precompiles are added, identifying them
    // as a precompile should be gated behind the revision they were activated
    // in.
    return is_eth_precompile<traits>(address) ||
           (address == staking::STAKING_CA) ||
           (traits::monad_rev() >= MONAD_NINE && address == RESERVE_BALANCE_CA)
        || (address == graph_eval::GRAPH_EVAL_CA);
}

EXPLICIT_MONAD_TRAITS(is_precompile);

template <Traits traits>
std::optional<evmc::Result> check_call_precompile(
    State &state, CallTracerBase &call_tracer, evmc_message const &msg)
{
    if (auto maybe_result = check_call_eth_precompile<traits>(msg)) {
        return maybe_result;
    }

#define CASE(cond, contract, addr)                                             \
    do {                                                                       \
        if constexpr ((cond)) {                                                \
            if (auto maybe_result =                                            \
                    check_call_monad_precompile<traits, contract, addr>(       \
                        state, call_tracer, msg)) {                            \
                return maybe_result;                                           \
            }                                                                  \
        }                                                                      \
    }                                                                          \
    while (false);

    CASE(
        traits::monad_rev() >= MONAD_FOUR,
        staking::StakingContract,
        staking::STAKING_CA);

    CASE(
        traits::monad_rev() >= MONAD_NINE,
        ReserveBalanceContract,
        RESERVE_BALANCE_CA);

    // TODO: PoC hack. Enabled from MONAD_NINE so blockchain test fixtures can
    // use the plain Ethereum state root (MIP-8 page-encoded storage starts at
    // MONAD_TEN). Must be MONAD_NEXT before merging.
    CASE(
        traits::monad_rev() >= MONAD_NINE,
        graph_eval::GraphEvalContract,
        graph_eval::GRAPH_EVAL_CA);

    return std::nullopt;

#undef CASE
}

EXPLICIT_MONAD_TRAITS(check_call_precompile);

MONAD_NAMESPACE_END
