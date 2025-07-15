#pragma once

#include <category/core/config.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <monad/vm/vm.hpp>

#include <quill/Quill.h>

#include <map>
#include <memory>

MONAD_NAMESPACE_BEGIN

class ProposalState
{
    std::unique_ptr<StateDeltas> state_;
    uint64_t parent_block_;
    bytes32_t parent_id_;

public:
    ProposalState(
        std::unique_ptr<StateDeltas> state, uint64_t const parent_block_number,
        bytes32_t const &parent_id)
        : state_(std::move(state))
        , parent_block_(parent_block_number)
        , parent_id_(parent_id)
    {
    }

    std::pair<uint64_t, bytes32_t> parent_info() const
    {
        return {parent_block_, parent_id_};
    }

    StateDeltas const &state() const
    {
        return *state_;
    }

    bool try_read_account(
        Address const &address, std::optional<Account> &result) const
    {
        StateDeltas::const_accessor it{};
        if (state_->find(it, address)) {
            result = it->second.account.second;
            return true;
        }
        return false;
    }

    bool try_read_storage(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key, bytes32_t &result) const
    {
        StateDeltas::const_accessor it{};
        if (!state_->find(it, address)) {
            return false;
        }
        auto const &account = it->second.account.second;
        if (!account || incarnation != account->incarnation) {
            result = {};
            return true;
        }
        auto const &storage = it->second.storage;
        StorageDeltas::const_accessor it2{};
        if (storage.find(it2, key)) {
            result = it2->second.second;
            return true;
        }
        return false;
    }
};

class Proposals
{
    using Key = std::pair<uint64_t, bytes32_t>; // <block_number, block_id>
    using Value = std::unique_ptr<ProposalState>;

    struct ProposalMapComparator
    {
        bool operator()(Key const &a, Key const &b) const
        {
            if (a.first != b.first) {
                return a.first < b.first;
            }
            return a.second < b.second;
        }
    };

    using ProposalMap = std::map<Key, Value, ProposalMapComparator>;

    static constexpr size_t MAX_PROPOSAL_MAP_SIZE = 100;

    ProposalMap proposal_map_{};
    uint64_t block_{0};
    bytes32_t block_id_{};
    uint64_t finalized_block_{0};
    bytes32_t finalized_block_id_{};

public:
    bool try_read_account(
        Address const &address, std::optional<Account> &result,
        bool &truncated) const
    {
        auto const fn = [&address, &result](ProposalState const &ps) {
            return ps.try_read_account(address, result);
        };
        return try_read(fn, truncated);
    }

    bool try_read_storage(
        Address const &address, Incarnation incarnation, bytes32_t const &key,
        bytes32_t &result, bool &truncated) const
    {
        auto const fn =
            [&address, incarnation, &key, &result](ProposalState const &ps) {
                return ps.try_read_storage(address, incarnation, key, result);
            };
        return try_read(fn, truncated);
    }

    void
    set_block_and_prefix(uint64_t const block_number, bytes32_t const &block_id)
    {
        block_ = block_number;
        block_id_ = block_id;
    }

    void commit(
        std::unique_ptr<StateDeltas> state_deltas, uint64_t const block_number,
        bytes32_t const &block_id)
    {
        if (proposal_map_.size() >= MAX_PROPOSAL_MAP_SIZE) {
            truncate_proposal_map();
        }
        auto const key = std::make_pair(block_number, block_id);
        MONAD_ASSERT(
            proposal_map_
                .insert(
                    {key,
                     std::unique_ptr<ProposalState>(new ProposalState(
                         std::move(state_deltas), block_, block_id_))})
                .second == true);
        block_ = block_number;
        block_id_ = block_id;
    }

    std::unique_ptr<ProposalState>
    finalize(uint64_t const block_num, bytes32_t const &block_id)
    {
        finalized_block_ = block_num;
        finalized_block_id_ = block_id;
        auto const it = proposal_map_.find(std::make_pair(block_num, block_id));
        if (it == proposal_map_.end()) {
            LOG_INFO(
                "Finalizing truncated proposal of block_id {}. Clear LRU "
                "caches.",
                block_id);
            return {};
        }
        std::unique_ptr<ProposalState> ps = std::move(it->second);
        // Clean up proposals earlier or equal to the finalized block
        for (auto it2 = proposal_map_.begin();
             it2->first.first <= finalized_block_ &&
             it2 != proposal_map_.end();) {
            it2 = proposal_map_.erase(it2);
        }
        return ps;
    }

private:
    template <class Func>
    bool try_read(Func const try_read_fn, bool &truncated) const
    {
        constexpr int DEPTH_LIMIT = 5;
        int depth = 1;
        bytes32_t block_id = block_id_;
        uint64_t block_number = block_;
        while (true) {
            if (block_id == finalized_block_id_) {
                break;
            }
            MONAD_ASSERT(block_number > finalized_block_);
            auto const it =
                proposal_map_.find(std::make_pair(block_number, block_id));
            if (it == proposal_map_.end()) {
                truncated = true;
                break;
            }
            ProposalState const *ps = it->second.get();
            MONAD_ASSERT(ps);
            if (try_read_fn(*ps)) {
                return true;
            }
            if (++depth > DEPTH_LIMIT) {
                truncated = true;
                break;
            }
            std::tie(block_number, block_id) = ps->parent_info();
        }
        return false;
    }

    void truncate_proposal_map()
    {
        MONAD_ASSERT(proposal_map_.size() == MAX_PROPOSAL_MAP_SIZE);
        // Remove the oldest proposal, the one with the smallest block number.
        // Note that there could be multiple proposals with the same block
        // number, here we randomly remove one of them.
        auto const it = proposal_map_.begin();
        LOG_INFO(
            "Round map size reached limit {}, truncating round {}",
            MAX_PROPOSAL_MAP_SIZE,
            it->first);
        proposal_map_.erase(it);
    }
};

MONAD_NAMESPACE_END
