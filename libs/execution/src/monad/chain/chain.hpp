#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/result.hpp>
#include <monad/execution/trace/call_tracer.hpp>

#include <evmc/evmc.h>
#include <optional>

MONAD_NAMESPACE_BEGIN

struct Account;
class BlockHashBuffer;
struct BlockHeader;
class BlockState;
struct Receipt;
class State;
struct Transaction;

struct Chain
{
    virtual ~Chain() = default;

    virtual uint256_t get_chain_id() const = 0;

    virtual evmc_revision get_revision(BlockHeader const &) const = 0;

    virtual Result<void> static_validate_header(BlockHeader const &) const;

    virtual Result<void> validate_header(
        std::vector<Receipt> const &, BlockHeader const &) const = 0;

    virtual bool validate_root(
        evmc_revision, BlockHeader const &, bytes32_t const &state_root,
        bytes32_t const &receipts_root) const = 0;

    virtual Result<void> validate_transaction(
        evmc_revision, Transaction const &, Address const &,
        std::optional<Account> const &) const = 0;

    virtual evmc::Result execute_impl_no_validation(
        CallTracerBase &, evmc_revision, BlockHashBuffer const &,
        BlockHeader const &, State &, Transaction const &,
        Address const &sender, std::optional<Account> const &) = 0;

    virtual Receipt execute_final(
        evmc_revision, State &, Transaction const &, Address const &sender,
        uint256_t const &base_fee_per_gas, evmc::Result const &,
        Address const &beneficiary) = 0;
};

MONAD_NAMESPACE_END
