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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/ecrecover.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/trace/event_trace.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

std::optional<Address> recover_authority(AuthorizationEntry const &auth_entry)
{
    byte_string const auth_encoding =
        rlp::encode_authorization_entry_for_signing(auth_entry);
    return recover_address(auth_entry.sc.signature, auth_encoding);
}

std::optional<Address> recover_sender(Transaction const &tx)
{
    TRACE_TXN_EVENT(StartSenderRecovery);
    byte_string const tx_encoding = rlp::encode_transaction_for_signing(tx);
    return recover_address(tx.sc.signature, tx_encoding);
}

MONAD_NAMESPACE_END
