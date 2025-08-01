#include "account.hpp"
#include "state.hpp"

#include <evmc/evmc.hpp>

namespace monad::vm::fuzzing
{
    void assert_equal(
        evmone::state::StorageValue const &a,
        evmone::state::StorageValue const &b);

    void assert_equal(
        evmone::state::Account const &a, evmone::state::Account const &b);

    void
    assert_equal(evmone::state::State const &a, evmone::state::State const &b);

    void assert_equal(
        evmc::Result const &evmone_result, evmc::Result const &compiler_result,
        bool strict_out_of_gas);
}
