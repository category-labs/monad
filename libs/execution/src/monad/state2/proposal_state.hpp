#pragma once

#include <monad/config.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/state2/state_deltas.hpp>

#include <quill/Quill.h>

#include <map>
#include <memory>

MONAD_NAMESPACE_BEGIN

class ProposalState
{
    std::unique_ptr<StateDeltas> state_;
    std::unique_ptr<Code> code_;
    uint64_t parent_;

public:
    ProposalState(
        std::unique_ptr<StateDeltas> &state, std::unique_ptr<Code> &code,
        uint64_t const parent)
        : state_(std::move(state))
        , code_(std::move(code))
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

    Code const &code() const
    {
        return *code_;
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
        Address const &address, Incarnation incarnation, bytes32_t const &key,
        bytes32_t &result) const
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

    bool try_read_code(
        bytes32_t const &code_hash, std::shared_ptr<CodeAnalysis> &result) const
    {
        Code::const_accessor it{};
        if (code_->find(it, code_hash)) {
            result = it->second;
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
    uint64_t last_finalized_{0};
    uint64_t round_{0};

public:
    bool try_read_account(
        Address const &address, std::optional<Account> &result,
        bool &truncated) const
    {
        auto fn = [&address, &result](ProposalState const &ps) {
            return ps.try_read_account(address, result);
        };
        return try_read(fn, truncated);
    }

    bool try_read_storage(
        Address const &address, Incarnation incarnation, bytes32_t const &key,
        bytes32_t &result, bool &truncated) const
    {
        auto fn =
            [&address, incarnation, &key, &result](ProposalState const &ps) {
                return ps.try_read_storage(address, incarnation, key, result);
            };
        return try_read(fn, truncated);
    }

    bool try_read_code(
        bytes32_t const &code_hash, std::shared_ptr<CodeAnalysis> &result,
        bool truncated) const
    {
        auto fn = [&code_hash, &result](ProposalState const &ps) {
            return ps.try_read_code(code_hash, result);
        };
        return try_read(fn, truncated);
    }

    void set_round(std::optional<uint64_t> round)
    {
        MONAD_ASSERT(!round.has_value() || round.value() >= last_finalized_);
        round_ = round.has_value() ? round.value() : last_finalized_;
    }

    void commit(
        std::unique_ptr<StateDeltas> &state_deltas, std::unique_ptr<Code> &code,
        std::optional<uint64_t> const round)
    {
        MONAD_ASSERT(round.has_value());
        if (round_map_.size() >= MAX_ROUND_MAP_SIZE) {
            truncate_round_map();
        }
        ProposalState *ptr{new ProposalState{state_deltas, code, round_}};
        auto const [it, _] = round_map_.insert_or_assign(
            round.value(), std::unique_ptr<ProposalState>(ptr));
        MONAD_ASSERT(it->first == round.value());
        MONAD_ASSERT(it->second.get() == ptr);
        round_ = round.value();
    }

    std::unique_ptr<ProposalState> finalize(uint64_t round)
    {
        last_finalized_ = round;
        round_ = round;
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
    bool try_read(Func try_read_fn, bool &truncated) const
    {
        MONAD_ASSERT(round_ >= last_finalized_);
        constexpr int DEPTH_LIMIT = 5;
        int depth = 1;
        uint64_t round = round_;
        while (round > last_finalized_) {
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
            MONAD_ASSERT(round >= last_finalized_);
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
