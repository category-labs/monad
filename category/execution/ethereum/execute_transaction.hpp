// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/fiber/future/promise.hpp>
#include <evmc/evmc.hpp>

#include <cstdint>
#include <type_traits>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
class BlockMetrics;
struct BlockHeader;
class BlockState;
struct CallTracerBase;
struct Chain;
template <Traits traits>
struct EvmcHost;
class State;
struct Transaction;

class RevertTransactionFn
{
public:
    RevertTransactionFn() noexcept;

    template <typename F>
    RevertTransactionFn(F &&fn)
        : storage_(new std::decay_t<F>(std::forward<F>(fn)))
        , vtable_(&vtable<std::decay_t<F>>())
    {
    }

    RevertTransactionFn(RevertTransactionFn const &);
    RevertTransactionFn &operator=(RevertTransactionFn const &);
    RevertTransactionFn(RevertTransactionFn &&) noexcept;
    RevertTransactionFn &operator=(RevertTransactionFn &&) noexcept;
    ~RevertTransactionFn();

    bool operator()(
        Address const &, Transaction const &, uint64_t, State &) const;

private:
    struct VTable
    {
        bool (*call)(
            void *, Address const &, Transaction const &, uint64_t, State &);
        void *(*clone)(void const *);
        void (*destroy)(void *);
    };

    template <typename T>
    static VTable const &vtable()
    {
        static VTable const instance{
            [](void *ptr,
               Address const &address,
               Transaction const &tx,
               uint64_t const index,
               State &state) -> bool {
                return (*static_cast<T *>(ptr))(address, tx, index, state);
            },
            [](void const *ptr) -> void * {
                return new T(*static_cast<T const *>(ptr));
            },
            [](void *ptr) {
                delete static_cast<T *>(ptr);
            }};
        return instance;
    }

    static VTable const &default_vtable()
    {
        static VTable const instance{
            [](void *,
               Address const &,
               Transaction const &,
               uint64_t,
               State &) -> bool { return false; },
            [](void const *) -> void * { return nullptr; },
            [](void *) {}};
        return instance;
    }

    friend void swap(RevertTransactionFn &, RevertTransactionFn &) noexcept;

    void *storage_;
    VTable const *vtable_;
};

inline RevertTransactionFn::RevertTransactionFn() noexcept
    : storage_(nullptr)
    , vtable_(&default_vtable())
{
}

inline RevertTransactionFn::RevertTransactionFn(
    RevertTransactionFn const &other)
    : storage_(
          other.storage_ != nullptr
              ? other.vtable_->clone(other.storage_)
              : nullptr)
    , vtable_(other.vtable_)
{
}

inline RevertTransactionFn &
RevertTransactionFn::operator=(RevertTransactionFn const &other)
{
    if (this != &other) {
        RevertTransactionFn temp(other);
        swap(*this, temp);
    }
    return *this;
}

inline RevertTransactionFn::RevertTransactionFn(
    RevertTransactionFn &&other) noexcept
    : storage_(other.storage_)
    , vtable_(other.vtable_)
{
    other.storage_ = nullptr;
    other.vtable_ = &default_vtable();
}

inline RevertTransactionFn &
RevertTransactionFn::operator=(RevertTransactionFn &&other) noexcept
{
    if (this != &other) {
        swap(*this, other);
    }
    return *this;
}

inline RevertTransactionFn::~RevertTransactionFn()
{
    if (storage_ != nullptr) {
        vtable_->destroy(storage_);
    }
}

inline bool RevertTransactionFn::operator()(
    Address const &address,
    Transaction const &tx,
    uint64_t const index,
    State &state) const
{
    return vtable_->call(storage_, address, tx, index, state);
}

inline void swap(RevertTransactionFn &lhs, RevertTransactionFn &rhs) noexcept
{
    using std::swap;
    swap(lhs.storage_, rhs.storage_);
    swap(lhs.vtable_, rhs.vtable_);
}

template <Traits traits>
class ExecuteTransactionNoValidation
{
    evmc_message to_message() const;

    uint64_t process_authorizations(State &, EvmcHost<traits> &);

protected:
    Chain const &chain_;
    Transaction const &tx_;
    Address const &sender_;
    std::vector<std::optional<Address>> const &authorities_;
    BlockHeader const &header_;
    uint64_t i_;
    RevertTransactionFn revert_transaction_;

public:
    ExecuteTransactionNoValidation(
        Chain const &, Transaction const &, Address const &,
        std::vector<std::optional<Address>> const &, BlockHeader const &,
        uint64_t i,
        RevertTransactionFn const & = RevertTransactionFn{});

    ExecuteTransactionNoValidation(
        Chain const &, Transaction const &, Address const &,
        BlockHeader const &);

    evmc::Result operator()(State &, EvmcHost<traits> &);
};

template <Traits traits>
class ExecuteTransaction : public ExecuteTransactionNoValidation<traits>
{
    using ExecuteTransactionNoValidation<traits>::chain_;
    using ExecuteTransactionNoValidation<traits>::tx_;
    using ExecuteTransactionNoValidation<traits>::sender_;
    using ExecuteTransactionNoValidation<traits>::authorities_;
    using ExecuteTransactionNoValidation<traits>::header_;
    using ExecuteTransactionNoValidation<traits>::i_;
    using ExecuteTransactionNoValidation<traits>::revert_transaction_;

    BlockHashBuffer const &block_hash_buffer_;
    BlockState &block_state_;
    BlockMetrics &block_metrics_;
    boost::fibers::promise<void> &prev_;
    CallTracerBase &call_tracer_;

    Result<evmc::Result> execute_impl2(State &);
    Receipt execute_final(State &, evmc::Result const &);

public:
    ExecuteTransaction(
        Chain const &, uint64_t i, Transaction const &, Address const &,
        std::vector<std::optional<Address>> const &, BlockHeader const &,
        BlockHashBuffer const &, BlockState &, BlockMetrics &,
        boost::fibers::promise<void> &prev, CallTracerBase &,
        RevertTransactionFn const & = RevertTransactionFn{});
    ~ExecuteTransaction() = default;

    Result<Receipt> operator()();
};

uint64_t g_star(
    evmc_revision, Transaction const &, uint64_t gas_remaining,
    uint64_t gas_refund);

MONAD_NAMESPACE_END
