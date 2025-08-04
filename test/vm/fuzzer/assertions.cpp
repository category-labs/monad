#include "account.hpp"
#include "state.hpp"

#include <category/vm/core/assert.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <algorithm>
#include <span>

using namespace evmone::state;

namespace monad::vm::fuzzing
{
    void assert_equal(StorageValue const &a, StorageValue const &b)
    {
        MONAD_VM_ASSERT(a.current == b.current);
        MONAD_VM_ASSERT(a.original == b.original);
        MONAD_VM_ASSERT(a.access_status == b.access_status);
    }

    void assert_equal(Account const &a, Account const &b)
    {
        MONAD_VM_ASSERT(
            a.transient_storage.size() == b.transient_storage.size());
        for (auto const &[k, v] : a.transient_storage) {
            auto const found = b.transient_storage.find(k);
            MONAD_VM_ASSERT(found != b.transient_storage.end());
            MONAD_VM_ASSERT(found->second == v);
        }

        MONAD_VM_ASSERT(a.storage.size() == b.storage.size());
        for (auto const &[k, v] : a.storage) {
            auto const found = b.storage.find(k);
            MONAD_VM_ASSERT(found != b.storage.end());
            assert_equal(v, found->second);
        }

        MONAD_VM_ASSERT(a.nonce == b.nonce);
        MONAD_VM_ASSERT(a.balance == b.balance);
        MONAD_VM_ASSERT(a.code_hash == b.code_hash);
        MONAD_VM_ASSERT(a.destructed == b.destructed);
        MONAD_VM_ASSERT(a.erase_if_empty == b.erase_if_empty);
        MONAD_VM_ASSERT(a.just_created == b.just_created);
        MONAD_VM_ASSERT(a.access_status == b.access_status);
    }

    void assert_equal(State const &a, State const &b)
    {
        auto const &a_accs = a.get_modified_accounts();
        auto const &b_accs = b.get_modified_accounts();

        MONAD_VM_ASSERT(a_accs.size() == b_accs.size());
        for (auto const &[k, v] : a_accs) {
            auto const found = b_accs.find(k);
            MONAD_VM_ASSERT(found != b_accs.end());
            assert_equal(v, found->second);
        }
    }

    void assert_equal(
        evmc::Result const &evmone_result, evmc::Result const &compiler_result,
        bool const strict_out_of_gas)
    {
        MONAD_VM_ASSERT(std::ranges::equal(
            evmone_result.create_address.bytes,
            compiler_result.create_address.bytes));

        MONAD_VM_ASSERT(evmone_result.gas_left == compiler_result.gas_left);
        MONAD_VM_ASSERT(evmone_result.gas_refund == compiler_result.gas_refund);

        MONAD_VM_ASSERT(std::ranges::equal(
            std::span(evmone_result.output_data, evmone_result.output_size),
            std::span(
                compiler_result.output_data, compiler_result.output_size)));

        switch (evmone_result.status_code) {
        case EVMC_SUCCESS:
        case EVMC_REVERT:
            MONAD_VM_ASSERT(
                evmone_result.status_code == compiler_result.status_code);
            break;
        case EVMC_OUT_OF_GAS: {
            if (strict_out_of_gas) {
                MONAD_VM_ASSERT(compiler_result.status_code == EVMC_OUT_OF_GAS);
            }
            else {
                // For the compiler, we allow a relaxed check for out-of-gas,
                // where it is permitted to resolve to either a generic failure
                // *or* an out-of-gas failure. This is because the compiler may
                // statically produce a generic error for code that would
                // dynamically run out of gas.
                MONAD_VM_ASSERT(
                    compiler_result.status_code == EVMC_OUT_OF_GAS ||
                    compiler_result.status_code == EVMC_FAILURE);
            }
            break;
        }
        default:
            MONAD_VM_ASSERT(compiler_result.status_code != EVMC_SUCCESS);
            MONAD_VM_ASSERT(compiler_result.status_code != EVMC_REVERT);
            break;
        }
    }

}
