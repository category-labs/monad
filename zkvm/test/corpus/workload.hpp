// Copyright (C) 2026 Category Labs, Inc.
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

#pragma once

// Benchmark corpora vary the distinct accounts touched per block. Mainnet
// measurements suggest witness size tracks distinct leaves, dominated by
// untouched-sibling digests. Sweep access shapes at equal distinct counts to
// test this hypothesis rather than assume equal proving costs.

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <zkvm/test/corpus/corpus_builder.hpp>

#include <cstdint>
#include <string>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace corpus
{
    class GenesisSink;

    /// Wholesale/Payouts use native EOA balances to isolate account-trie
    /// accesses. WholesaleCbdc/WorkerPayouts use eligibility-gated wrapped
    /// tokens, so holder balances are storage slots. WholesaleCbdc settles
    /// two currency legs atomically via PvpSettlement. WorkerPayouts models
    /// payroll, the earn vault and card/redemption/L1 exits. Wholesale has
    /// hundreds of institutions; payouts targets million-holder scale.
    enum class Preset
    {
        Wholesale,
        Payouts,
        WholesaleCbdc,
        WorkerPayouts,
    };

    /// Access distributions: Uniform spreads reads; Zipf concentrates on a
    /// head; HotSet restricts draws to a fixed subset.
    enum class Shape
    {
        Uniform,
        Zipf,
        HotSet,
    };

    Preset preset_from_name(std::string const &);
    Shape shape_from_name(std::string const &);
    char const *name_of(Preset);
    char const *name_of(Shape);

    struct WorkloadSpec
    {
        Preset preset{Preset::Payouts};
        Shape shape{Shape::Zipf};
        /// Genesis accounts, or token-preset participants
        /// (banks/contractors). Zero selects the preset default through
        /// resolved().
        uint64_t accounts{0};
        /// Blocks to emit after the deploy block -- after the warm-up, in an L2
        /// build, which has no deploy block.
        uint64_t blocks{200};
        /// L2 blocks executed but not emitted before measurement, to fill the
        /// 256-entry history window. Ancestors::All then has a steady-state
        /// size. Always zero outside L2 builds.
#ifdef MONAD_ZKVM_L2
        uint64_t warmup{BlockHashBuffer::N};
#else
        uint64_t warmup{0};
#endif
        /// Distinct accounts a block aims to touch -- banks or contractors
        /// for the token presets. THE axis. Zero means the preset's default,
        /// as above.
        uint64_t distinct{0};
        /// WholesaleCbdc only: the currencies the platform settles, one
        /// wrapped token each, held by their own banks and by every
        /// intermediary. Zero means the default, five.
        uint64_t currencies{0};
        double zipf_s{1.1};
        /// Accounts per genesis commit. See genesis_bulk.hpp: a StateDelta is
        /// 752 bytes whether or not the account has storage.
        size_t chunk{100'000};
        bytes32_t seed{};

        /// The defaults the preset implies, applied for any field the caller
        /// left at its own default. Returns a spec with nothing left implicit.
        WorkloadSpec resolved() const;

        /// A gas limit that fits `distinct` transfers with room to spare. A
        /// block touching thousands of accounts does not fit under 30M, and
        /// the header's limit is constant for the chain.
        uint64_t gas_limit() const;
    };

    /// Fill a genesis with this workload's accounts. Deterministic in
    /// `spec.seed`.
    void seed_workload(GenesisSink &, WorkloadSpec const &);

    /// Execute and emit workload blocks. L2 seeds the spoke at genesis zero
    /// and suppresses the first warmup blocks. Ethereum first emits a
    /// deployment block using the deployer/nonce reported by --spoke-address.
    class Workload
    {
    public:
        explicit Workload(WorkloadSpec);

        /// The genesis seeder to hand CorpusBuilder's bulk constructor.
        std::function<void(GenesisSink &)> seeder() const;

        /// The spoke address: the compiled MONAD_ZKVM_L2_SPOKE in an L2 build,
        /// and otherwise where the deploy block's CREATE puts it, known before
        /// any block runs because a CREATE address is a function of deployer
        /// and nonce.
        Address spoke() const;

        /// The next block's transactions, or an empty spec once the run is
        /// done. `index` counts from 0; outside an L2 build, 0 is the deploy
        /// block.
        BlockSpec block(CorpusBuilder &, uint64_t index);

        /// Total blocks the run executes: the warm-up and the emitted ones,
        /// or the deploy block and the emitted ones.
        uint64_t block_count() const;

        /// Whether block `index` is one to emit rather than warm-up.
        bool measured(uint64_t index) const;

        WorkloadSpec const &spec() const
        {
            return spec_;
        }

        /// Intended distinct participants in the last block, before
        /// execution. Token balances are storage slots, not account leaves;
        /// compare this request with the witness's measured counts.
        uint64_t last_intended_distinct() const
        {
            return last_distinct_;
        }

        /// Token presets: where the seeded contracts live. For WholesaleCbdc
        /// `token(c)` is currency c's reserves, the first currency the one on
        /// one side of most payments. For WorkerPayouts `token(0)` is the
        /// contractors' dollar token and `token(1)` the businesses'
        /// stablecoin.
        Address token(uint64_t index) const;
        Address settlement() const;
        Address vault() const;

    private:
        /// WholesaleCbdc: a payment proposed in one block, which its
        /// intermediary settles in the next -- the banks it touches, by
        /// index, and the call that settles it.
        struct Proposal
        {
            uint64_t debtor;
            uint64_t intermediary;
            uint64_t creditor;
            byte_string settle;
        };

        BlockSpec wholesale_cbdc_block(uint64_t index);
        BlockSpec worker_payouts_block(uint64_t index);

        WorkloadSpec spec_;
        uint64_t last_distinct_{0};

        /// Cache signer addresses to avoid repeated EC multiplication in
        /// calldata construction: banks for WholesaleCbdc, active contractors
        /// for WorkerPayouts.
        std::vector<Address> signers_;
        /// WorkerPayouts: the businesses that fund payroll.
        std::vector<Address> businesses_;
        /// WholesaleCbdc: the last block's proposals, for this one to settle.
        std::vector<Proposal> proposed_;
        /// WorkerPayouts: contractors admitted since genesis.
        uint64_t onboarded_{0};
    };
}

MONAD_NAMESPACE_END
