// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <test/utils/from_json.hpp>
#include <test/utils/json_state.hpp>
#include <test/utils/test_state.hpp>
#include <test/vm/utils/benchmark_vm.hpp>

#include <ankerl/unordered_dense.h>
#include <benchmark/benchmark.h>
#include <nlohmann/json.hpp>

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <format>
#include <fstream>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

namespace fs = std::filesystem;

using namespace monad;

namespace
{
    using AddressSet = ankerl::unordered_dense::segmented_set<Address>;

    fiber::PriorityPool *pool = nullptr;

    struct Fixture
    {
        nlohmann::json json;
        Block block;
        std::vector<Address> senders;
        std::vector<std::vector<std::optional<Address>>> authorities;
        AddressSet senders_and_authorities;
        std::vector<AddressSet> ancestor_senders_and_authorities;
        std::vector<std::pair<uint64_t, bytes32_t>> block_hashes;
    };

    Block decode_block(nlohmann::json const &rlp_json)
    {
        auto const rlp = rlp_json.get<byte_string>();
        byte_string_view view{rlp};
        auto block = rlp::decode_block(view);
        MONAD_ASSERT(!block.has_error() && view.empty());
        return std::move(block.value());
    }

    std::vector<Address> recover_all_senders(Block const &block)
    {
        std::vector<Address> senders;
        for (auto const &sender : recover_senders(block.transactions, *pool)) {
            MONAD_ASSERT(sender.has_value());
            senders.push_back(sender.value());
        }
        return senders;
    }

    std::unique_ptr<Fixture> load_fixture(fs::path const &path)
    {
        std::ifstream in{path};
        auto const file = nlohmann::json::parse(in);
        MONAD_ASSERT(file.size() == 1);

        auto fixture = std::make_unique<Fixture>();
        fixture->json = file.begin().value();
        fixture->block =
            decode_block(fixture->json.at("blocks").at(0).at("rlp"));
        fixture->senders = recover_all_senders(fixture->block);
        fixture->authorities =
            recover_authorities(fixture->block.transactions, *pool);
        fixture->senders_and_authorities = combine_senders_and_authorities(
            fixture->senders, fixture->authorities);

        for (auto const &rlp :
             fixture->json.at("_replay").at("ancestorBlocks")) {
            auto const ancestor = decode_block(rlp);
            fixture->block_hashes.emplace_back(
                ancestor.header.number - 1, ancestor.header.parent_hash);
            fixture->ancestor_senders_and_authorities.push_back(
                combine_senders_and_authorities(
                    recover_all_senders(ancestor),
                    recover_authorities(ancestor.transactions, *pool)));
        }
        MONAD_ASSERT(fixture->ancestor_senders_and_authorities.size() == 2);
        fixture->block_hashes.emplace_back(
            fixture->block.header.number - 1,
            fixture->block.header.parent_hash);
        return fixture;
    }

    template <Traits traits>
    struct Loaded
    {
        fs::path path;
        std::unique_ptr<Fixture> fixture;
        test::TestStateRef<traits::mip_8_active()> state;
    };

    template <Traits traits>
    Loaded<traits> &load(fs::path const &path)
    {
        static Loaded<traits> loaded;
        if (loaded.path != path) {
            loaded = {};
            auto fixture = load_fixture(path);
            auto const json_state =
                test::load_blockchain_json_state<traits>(fixture->json);
            loaded.state =
                json_state.template make_test_state<traits::mip_8_active()>();
            loaded.fixture = std::move(fixture);
            loaded.path = path;
        }
        return loaded;
    }

    template <Traits traits>
    std::vector<Receipt> execute(
        Fixture const &fixture, Db &db, vm::VM &vm,
        BlockHashBuffer const &block_hash_buffer)
    {
        auto const n = fixture.block.transactions.size();
        std::vector<std::unique_ptr<CallTracerBase>> call_tracers;
        std::vector<std::unique_ptr<trace::StateTracer>> state_tracers;
        for (size_t i = 0; i < n; ++i) {
            call_tracers.push_back(std::make_unique<NoopCallTracer>());
            state_tracers.push_back(
                std::make_unique<trace::StateTracer>(std::monostate{}));
        }
        trace::StateTracer system_call_state_tracer{std::monostate{}};
        ChainContext<traits> const chain_context{
            .grandparent_senders_and_authorities =
                fixture.ancestor_senders_and_authorities[0],
            .parent_senders_and_authorities =
                fixture.ancestor_senders_and_authorities[1],
            .senders_and_authorities = fixture.senders_and_authorities,
            .senders = fixture.senders,
            .authorities = fixture.authorities};

        BlockState block_state{db, vm};
        BlockMetrics metrics;
        auto receipts = execute_block<traits>(
            MonadMainnet{},
            fixture.block,
            fixture.senders,
            fixture.authorities,
            block_state,
            block_hash_buffer,
            pool->fiber_group(),
            metrics,
            call_tracers,
            state_tracers,
            system_call_state_tracer,
            chain_context,
            nullptr);
        MONAD_ASSERT(!receipts.has_error());
        return std::move(receipts.value());
    }

    template <Traits traits>
    void
    run(benchmark::State &state, fs::path const &path, vm::VM::Mode const mode)
    {
        auto &loaded = load<traits>(path);
        auto const &fixture = *loaded.fixture;
        auto &db = loaded.state->trie_db;

        BlockHashBufferFinalized block_hash_buffer;
        for (auto const &[number, hash] : fixture.block_hashes) {
            block_hash_buffer.set(number, hash);
        }

        vm::VM vm{mode};
        auto const receipts =
            execute<traits>(fixture, db, vm, block_hash_buffer);
        auto const &header = fixture.block.header;
        MONAD_ASSERT(receipts.size() == fixture.block.transactions.size());
        MONAD_ASSERT(compute_bloom(receipts) == header.logs_bloom);
        MONAD_ASSERT(
            (receipts.empty() ? 0 : receipts.back().gas_used) ==
            header.gas_used);
        vm.compiler().debug_wait_for_empty_queue();

        for (auto _ : state) {
            benchmark::DoNotOptimize(
                execute<traits>(fixture, db, vm, block_hash_buffer));
        }
        state.counters["txs"] =
            static_cast<double>(fixture.block.transactions.size());
    }

    void run_revision(
        benchmark::State &state, fs::path const &path, vm::VM::Mode const mode,
        monad_revision const rev)
    {
        SWITCH_MONAD_TRAITS(run, state, path, mode);
        MONAD_ASSERT(false);
    }

    monad_revision fixture_revision(fs::path const &path)
    {
        std::ifstream in{path};
        auto const file = nlohmann::json::parse(in);
        auto const timestamp = std::stoull(
            file.begin()
                .value()
                .at("_replay")
                .at("timestamp")
                .get<std::string>(),
            nullptr,
            0);
        return MonadMainnet{}.get_monad_revision(timestamp);
    }

    unsigned env_or(char const *const name, unsigned const fallback)
    {
        char const *const value = std::getenv(name);
        return value ? static_cast<unsigned>(std::atoi(value)) : fallback;
    }
}

int main(int argc, char **argv)
{
    benchmark::Initialize(&argc, argv);

    char const *const dir = std::getenv("MONAD_REPLAY_FIXTURES");
    if (dir == nullptr || argc > 1) {
        std::fprintf(
            stderr,
            "usage: MONAD_REPLAY_FIXTURES=<dir> %s [benchmark flags]\n",
            argv[0]);
        return 1;
    }

    MONAD_ASSERT(init_trusted_setup());
    fiber::PriorityPool priority_pool{
        env_or("MONAD_REPLAY_THREADS", 1), env_or("MONAD_REPLAY_FIBERS", 1)};
    pool = &priority_pool;

    std::vector<fs::path> paths;
    for (auto const &entry : fs::directory_iterator(dir)) {
        if (entry.path().extension() == ".json") {
            paths.push_back(entry.path());
        }
    }
    std::ranges::sort(paths);

    for (auto const &path : paths) {
        auto const rev = fixture_revision(path);
        for (auto const mode :
             {vm::VM::InterpreterOnly, vm::VM::CompilerOnly}) {
            benchmark::RegisterBenchmark(
                std::format(
                    "replay/{}/{}",
                    path.stem().string(),
                    vm::test::impl_name(mode)),
                run_revision,
                path,
                mode,
                rev)
                ->Unit(benchmark::kMicrosecond)
                ->UseRealTime();
        }
    }

    benchmark::RunSpecifiedBenchmarks();
    benchmark::Shutdown();
    pool = nullptr;
}
