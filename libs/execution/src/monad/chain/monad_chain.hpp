#pragma once

#include <monad/chain/chain.hpp>
#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/execution/trace/call_tracer.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct Account;
struct BlockHeader;
class IntrinsicGasBuffer;
struct Transaction;

class MonadChain : public Chain
{
    IntrinsicGasBuffer &buf_;
    uint256_t default_max_reserve_;

public:
    explicit MonadChain(
        IntrinsicGasBuffer &, uint256_t const &default_max_reserve);

    Result<void> validate_header(
        std::vector<Receipt> const &, BlockHeader const &) const override;

    virtual bool validate_root(
        evmc_revision, BlockHeader const &, bytes32_t const &state_root,
        bytes32_t const &receipts_root) const override;

    virtual Result<void> validate_transaction(
        evmc_revision, Transaction const &, Address const &,
        std::optional<Account> const &) const override;

    virtual std::pair<evmc::Result, TxnCallFrames> execute_impl_no_validation(
        evmc_revision, BlockHashBuffer const &, BlockHeader const &, State &,
        Transaction const &, Address const &sender,
        std::optional<Account> const &) override;

    virtual Receipt execute_final(
        evmc_revision, State &, Transaction const &, Address const &sender,
        uint256_t const &base_fee_per_gas, evmc::Result const &,
        Address const &beneficiary) override;
};

MONAD_NAMESPACE_END
