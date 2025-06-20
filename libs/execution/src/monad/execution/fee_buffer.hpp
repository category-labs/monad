#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/int.hpp>

#include <ankerl/unordered_dense.h>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#include <immer/array.hpp>
#pragma GCC diagnostic pop

#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

constexpr unsigned EXECUTION_DELAY = 3;

class FeeBuffer
{
    using Fees = ankerl::unordered_dense::segmented_map<
        Address, std::vector<std::pair<unsigned, uint512_t>>>;
    using ProposalFees = immer::array<Fees>;

    ankerl::unordered_dense::segmented_map<uint64_t, ProposalFees> proposals_{};
    uint64_t block_number_{0};
    uint64_t round_{0};
    uint64_t parent_round_{0};
    Fees fees_{};

public:
    void set(uint64_t block_number, uint64_t round, uint64_t parent_round);
    void note(unsigned i, Address const &, uint512_t fee);
    void propose();
    void finalize(uint64_t round);
    uint512_t sum(unsigned i, Address const &) const;
};

static_assert(sizeof(FeeBuffer) == 152);
static_assert(alignof(FeeBuffer) == 8);

MONAD_NAMESPACE_END
