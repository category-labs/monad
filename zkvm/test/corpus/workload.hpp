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

// A benchmark corpus at scale: a large genesis, then blocks that move value
// around it, shaped after the two use cases the L2 design document names.
//
// The axis is `distinct` -- how many distinct accounts a block touches -- and
// that choice is a measurement, not a preference. Over 504 mainnet witnesses
// joined to their measured cost, 82% of a witness is 33-byte digests of
// siblings the block never touched, and cost tracks witness bytes with
// R2 0.94. A leaf touched twice in one block is free: it is already in the
// witness. So the shape of the access distribution can only matter through the
// number of DISTINCT leaves it produces -- which is why `distinct` is the
// parameter swept, and why `shape` exists to TEST that prediction rather than
// to choose between hypotheses. Two shapes at equal `distinct` should cost the
// same; if they do not, the reasoning above is wrong and that is a result.

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

    /// Which of the design document's two use cases to generate, and in which
    /// form. The two are inverse in the parameter that costs: wholesale is
    /// hundreds of institutions moving large amounts, payouts is over a
    /// million holders a platform pays out to. Wholesale is the cheap end;
    /// payouts is the one sizing has to be done against.
    ///
    /// Each comes twice. Wholesale and Payouts move value as native balances
    /// between EOAs, so a holder is an account leaf and nothing else is: the
    /// cleaner experiment on one trie, and the one the dispersion law was
    /// fitted on. WholesaleCbdc and WorkerPayouts follow the document's own
    /// flows instead. Value is an ERC-20 per natively wrapped L1 token --
    /// contracts/WrappedToken.sol, eligibility enforced in the token -- so a
    /// holder is a storage slot. WholesaleCbdc settles cross-currency payments
    /// between `currencies` wrapped reserve tokens payment-versus-payment,
    /// both legs in one transaction (contracts/PvpSettlement.sol).
    /// WorkerPayouts funds payroll from
    /// businesses, pays contractors in batches, and carries the earn vault
    /// (contracts/EarnVault.sol) and the document's three exits: card,
    /// redemption and withdrawal to the L1.
    enum class Preset
    {
        Wholesale,
        Payouts,
        WholesaleCbdc,
        WorkerPayouts,
    };

    /// How a block picks the accounts it touches. Uniform is the pessimistic
    /// bound -- no two draws share a trie path below the top few levels. Zipf
    /// concentrates on a head, which is what a real payout run looks like.
    /// HotSet draws from a fixed subset, which models "how many distinct
    /// beneficiaries per block" without committing to a law.
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
        /// Accounts in the genesis state -- for the token presets, the
        /// participants: banks for WholesaleCbdc, contractors for
        /// WorkerPayouts. Zero means "the preset's own default" -- zero
        /// accounts is meaningless, so it carries no other reading, and
        /// `resolved()` is what turns it into a number.
        uint64_t accounts{0};
        /// Blocks to emit after the deploy block -- after the warm-up, in an L2
        /// build, which has no deploy block.
        uint64_t blocks{200};
        /// L2 builds: blocks executed before the first emitted one, so every
        /// emitted witness carries the ancestor headers a chain in its steady
        /// state carries -- the block hash buffer's 256 -- rather than the
        /// handful a chain just out of genesis has. Each costs about 0.35 M
        /// COST, so a corpus that starts at genesis understates small blocks.
        /// Always zero outside an L2 build.
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

    /// Drives a builder through the workload's blocks, emitting each.
    ///
    /// In an L2 build the chain is the L2's own: genesis is block 0 and holds
    /// the NamespaceSpoke at the address the guest is compiled with, as the
    /// design creates it with the L2, so every block is a workload block --
    /// the first `warmup` of them executed and not emitted.
    ///
    /// Outside one, block 0 of the run deploys the spoke -- from the same key
    /// and nonce `--spoke-address` prints -- and is reported like any other,
    /// since it is a real block.
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

        /// Distinct accounts the last `block()` call aimed to touch, before
        /// execution -- for the token presets, the participants whose balances
        /// it moves, which are slots and not accounts. The witness's own count
        /// is the measurement; this is what was asked for, and the two
        /// differing is worth seeing.
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

        /// Token presets only: the address behind every key a block signs
        /// with, derived once -- each is an EC multiplication, and a block
        /// names hundreds of them in its calldata. Banks for WholesaleCbdc;
        /// for WorkerPayouts, the contractors who send.
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
