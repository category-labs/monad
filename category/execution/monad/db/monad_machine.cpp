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

#include <category/execution/monad/db/monad_machine.hpp>

#include <category/core/assert.h>
#include <category/execution/ethereum/db/storage_page.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/mpt/compute.hpp>
#include <category/mpt/node.hpp>

MONAD_NAMESPACE_BEGIN

using namespace monad::mpt;

namespace
{
    struct MonadStorageLeafProcessor
    {
        static byte_string process(Node const &node)
        {
            MONAD_ASSERT(node.has_value());
            auto encoded_storage = node.value();
            auto const storage = decode_storage_db(encoded_storage);
            MONAD_ASSERT(!storage.has_error());
            auto const page =
                decode_storage_value<storage_page_t>(storage.value().second);
            auto const commitment = page_commit(page);
            return rlp::encode_string2(
                {commitment.bytes, sizeof(commitment.bytes)});
        }
    };

    using MonadStorageMerkleCompute =
        MerkleComputeBase<MonadStorageLeafProcessor>;
} // namespace

mpt::Compute &MonadInMemoryMachine::get_compute() const
{
    static MonadStorageMerkleCompute monad_storage_compute;
    auto const prefix_length = prefix_len();
    if (revision >= MONAD_NEXT && table == TableType::State &&
        depth > prefix_length + 2 * sizeof(bytes32_t)) {
        return monad_storage_compute;
    }
    return InMemoryMachine::get_compute();
}

std::unique_ptr<StateMachine> MonadInMemoryMachine::clone() const
{
    return std::make_unique<MonadInMemoryMachine>(*this);
}

mpt::Compute &MonadOnDiskMachine::get_compute() const
{
    static MonadStorageMerkleCompute monad_storage_compute;
    auto const prefix_length = prefix_len();
    if (revision >= MONAD_NEXT && table == TableType::State &&
        depth > prefix_length + 2 * sizeof(bytes32_t)) {
        return monad_storage_compute;
    }
    return OnDiskMachine::get_compute();
}

std::unique_ptr<StateMachine> MonadOnDiskMachine::clone() const
{
    return std::make_unique<MonadOnDiskMachine>(*this);
}

MONAD_NAMESPACE_END
