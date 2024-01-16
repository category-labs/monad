#include <monad/state3/account_state.hpp>

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>

MONAD_NAMESPACE_BEGIN

AccountState::AccountState(Address const &address, BlockState &block_state)
    : address_{address}
    , block_state_{block_state}
    , state_delta_{
          .account =
              [this] {
                  auto const account = block_state_.read_account(address_);
                  return AccountDelta{account, account};
              }(),
          .storage = {}}
{
}

MONAD_NAMESPACE_END
