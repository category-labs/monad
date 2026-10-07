// Copyright (C) 2026 Category Labs, Inc.
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

// Signing transactions, for the corpus generator. Nothing in the production
// tree signs one -- a node verifies signatures, it does not produce them --
// so this exists only to make a corpus whose senders recover.

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/transaction.hpp>

MONAD_NAMESPACE_BEGIN

namespace corpus
{
    /// The address `recover_sender` will report for a transaction signed with
    /// this secret: the chain's address hash of the uncompressed public key,
    /// low 20 bytes (signature_hash.hpp).
    Address address_of(bytes32_t const &secret);

    /// Sign tx so recover_sender(tx) == address_of(secret), using
    /// rlp::encode_transaction_for_signing. Finalize all signed fields first,
    /// including chain id, nonce, fees, gas, destination/value/data and
    /// lists.
    void sign_transaction(Transaction &tx, bytes32_t const &secret);
}

MONAD_NAMESPACE_END
