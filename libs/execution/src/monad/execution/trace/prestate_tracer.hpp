#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/state3/account_state.hpp>

#include <ankerl/unordered_dense.h>

#include <nlohmann/json.hpp>

MONAD_NAMESPACE_BEGIN

class State;
struct Transaction;

struct PrestateTracerBase
{
    template <class Key, typename T>
    using Map = ankerl::unordered_dense::segmented_map<Key, T>;

    virtual Map<Address, AccountState> &&get_pre_state() = 0;
    virtual StateDeltas &&get_state_deltas() = 0;

    virtual ~PrestateTracerBase() = default;
};

struct NoopPrestateTracer final : public PrestateTracerBase
{
    virtual Map<Address, AccountState> &&get_pre_state() override;
    virtual StateDeltas &&get_state_deltas() override;

    Map<Address, AccountState> null_pre_state_;
    StateDeltas null_state_deltas_;
};

class PrestateTracer final : public PrestateTracerBase
{
    Map<Address, AccountState> pre_state_;
    StateDeltas state_deltas_;

public:
    PrestateTracer() = delete;
    PrestateTracer(PrestateTracer const &) = delete;
    PrestateTracer(PrestateTracer &&) = delete;
    explicit PrestateTracer(State const &state);

    virtual Map<Address, AccountState> &&get_pre_state() override;
    virtual StateDeltas &&get_state_deltas() override;
};

using PreState = PrestateTracerBase::Map<Address, AccountState>;

nlohmann::json state_to_json(PreState const &, State &);
nlohmann::json state_deltas_to_json(StateDeltas const &, State &);

// debug methods
nlohmann::json
state_to_json_with_tx_hash(PreState const &, Transaction const &, State &);
nlohmann::json state_deltas_to_json_with_tx_hash(
    StateDeltas const &, Transaction const &, State &);

MONAD_NAMESPACE_END
