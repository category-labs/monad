#pragma once

#include <monad/config.hpp>
#include <monad/state2/state_deltas.hpp>

#include <quill/Quill.h>

#include <map>
#include <memory>

MONAD_NAMESPACE_BEGIN

class ProposalState
{
    std::unique_ptr<StateDeltas> state_;
    uint64_t parent_;

public:
    ProposalState(
        std::unique_ptr<StateDeltas> state, uint64_t const parent)
        : state_(std::move(state))
        , parent_(parent)
    {
    }

    uint64_t parent() const
    {
        return parent_;
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
    using RoundMap = std::map<uint64_t, std::unique_ptr<ProposalState>>;

    static constexpr size_t MAX_ROUND_MAP_SIZE = 100;

    RoundMap round_map_{};
    uint64_t block_{0};
    std::optional<uint64_t> round_{0};
    uint64_t finalized_block_{0};
    uint64_t finalized_round_{0};

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

    void set_block_and_round(
        uint64_t const block_number, std::optional<uint64_t> const round)
    {
        block_ = block_number;
        round_ = round;
    }

    void commit(
        std::unique_ptr<StateDeltas> state_deltas, uint64_t const round)
    {
        if (round_map_.size() >= MAX_ROUND_MAP_SIZE) {
            truncate_round_map();
        }
        round_map_.insert_or_assign(
            round,
            std::unique_ptr<ProposalState>(new ProposalState(
                std::move(state_deltas),
                round_ ? round_.value() : finalized_round_)));
        round_ = round;
    }

    std::unique_ptr<ProposalState>
    finalize(uint64_t const block_num, uint64_t const round)
    {
        finalized_block_ = block_num;
        finalized_round_ = round;
        auto const it = round_map_.find(round);
        if (it == round_map_.end()) {
            LOG_INFO("Finalizing truncated round {}. Clear LRU caches.", round);
            return {};
        }
        MONAD_ASSERT(it->first == round);
        auto it2 = round_map_.begin();
        while (it2 != it) {
            MONAD_ASSERT(it2->first < round);
            MONAD_ASSERT(it2->second);
            it2 = round_map_.erase(it2);
        }
        std::unique_ptr<ProposalState> ps = std::move(it->second);
        MONAD_ASSERT(ps);
        round_map_.erase(it);
        return ps;
    }

private:
    template <class Func>
    bool try_read(Func const try_read_fn, bool &truncated) const
    {
        constexpr int DEPTH_LIMIT = 5;
        int depth = 1;
        uint64_t round = round_.has_value() ? round_.value() : finalized_round_;
        while (true) {
            if (round <= finalized_round_) {
                // TODO: Revisit when rewind is disallowed.
                if (round < finalized_round_) {
                    truncated = true;
                }
                break;
            }
            auto const it = round_map_.find(round);
            if (it == round_map_.end()) {
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
            round = ps->parent();
        }
        return false;
    }

    void truncate_round_map()
    {
        MONAD_ASSERT(round_map_.size() == MAX_ROUND_MAP_SIZE);
        auto const it = round_map_.begin();
        LOG_INFO(
            "Round map size reached limit {}, truncating round {}",
            MAX_ROUND_MAP_SIZE,
            it->first);
        round_map_.erase(it);
    }
};

MONAD_NAMESPACE_END
