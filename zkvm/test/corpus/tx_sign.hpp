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
    /// this secret: keccak of the uncompressed public key, low 20 bytes.
    Address address_of(bytes32_t const &secret);

    /// Fill tx.sc.signature so that recover_sender(tx) == address_of(secret).
    ///
    /// The preimage is not reconstructed here, it is taken from
    /// rlp::encode_transaction_for_signing -- the same call recover_sender
    /// makes. Two encoders that must agree is how the field-order bug in the
    /// node blob happened; one encoder cannot disagree with itself.
    ///
    /// tx.sc.chain_id must already be set for a typed transaction (the type
    /// byte and the chain id are both inside the preimage), and everything
    /// else that the preimage covers -- nonce, fees, gas limit, to, value,
    /// data, access list, authorization list -- must be final. Signing last is
    /// not a convention here, it is forced.
    void sign_transaction(Transaction &tx, bytes32_t const &secret);
}

MONAD_NAMESPACE_END
