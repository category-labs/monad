#pragma once

#include <category/execution/ethereum/core/address.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct CallTracerBase;
struct Chain;
class EvmcHostBase;
class State;

template <evmc_revision rev>
class Create
{
    Chain const &chain_;
    State &state_;
    BlockHeader const &header_;
    CallTracerBase &call_tracer_;

public:
    Create(Chain const &, State &, BlockHeader const &, CallTracerBase &);

    evmc::Result operator()(EvmcHostBase &, evmc_message const &) noexcept;
    evmc::Result deploy_contract_code(Address const &, evmc::Result) noexcept;
};

template <evmc_revision rev>
class Call
{
    State &state_;
    CallTracerBase &call_tracer_;
    Chain const &chain_;
    uint64_t i_;
    void *chain_context_;

    std::optional<evmc::Result>
    pre_call(EvmcHostBase const &, evmc_message const &);
    void post_call(evmc::Result const &);

public:
    Call(State &, CallTracerBase &, Chain const &, uint64_t, void *);

    evmc::Result operator()(EvmcHostBase &, evmc_message const &) noexcept;
};

MONAD_NAMESPACE_END
