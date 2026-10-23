// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/db/lbt_machine.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/compute.hpp>
#include <category/mpt/lbt/commit.hpp>
#include <category/mpt/lbt/compute.hpp>
#include <category/mpt/lbt/key_path.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/state_machine_kind.hpp>

#include <cstdint>
#include <memory>
#include <optional>
#include <span>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// The account's DB encoding (encode_account_db), followed by its storage
// root when it has storage. Provisional: the account/storage split replaces
// this leaf.
struct AccountValueHasher
{
    static bytes32_t hash(mpt::Node const &node)
    {
        byte_string bytes{node.value()};
        bytes += node.data();
        return mpt::lbt::value_hash(bytes);
    }
};

struct PageValueHasher
{
    static bytes32_t hash(mpt::Node const &node)
    {
        auto const page = decode_storage_leaf_to_page(node.value(), true);
        // Writers delete empty pages; one here would commit a leaf the
        // state does not have.
        MONAD_ASSERT(!page.is_empty());
        return page_commit(page);
    }
};

// TrieDb::state_root() reads the table's commitment from the root's own
// data, which only a value-bearing node has.
struct TableRootCompute final : public mpt::lbt::LbtDataCompute
{
    virtual unsigned compute_node_data_len(
        std::span<mpt::ChildData> const children, uint16_t const mask,
        mpt::NibblesView const path,
        std::optional<byte_string_view> const value) override
    {
        MONAD_ASSERT(value.has_value());
        return LbtDataCompute::compute_node_data_len(
            children, mask, path, value);
    }
};

enum class StateLevel : uint8_t
{
    table_root,
    account,
    storage,
};

struct StatePosition
{
    StateLevel level;
    unsigned key_start; // depth at which the current key begins
};

// The deepest State node: proposal prefix, account key, storage key.
static_assert(
    mpt::lbt::KeyPath::CAPACITY >=
    MachineBase::PROPOSAL_PREFIX_LEN + 2 * mpt::lbt::KEY_NIBBLES);

StatePosition state_position(MachineBase const &m)
{
    MONAD_ASSERT(m.table == MachineBase::TableType::State);
    unsigned const table_start = m.prefix_len();
    MONAD_ASSERT(m.depth >= table_start);
    if (m.depth == table_start) {
        return {.level = StateLevel::table_root, .key_start = table_start};
    }
    unsigned const account_end = table_start + mpt::lbt::KEY_NIBBLES;
    if (m.depth <= account_end) {
        return {.level = StateLevel::account, .key_start = table_start};
    }
    return {.level = StateLevel::storage, .key_start = account_end};
}

mpt::Compute &state_compute(MachineBase const &m, mpt::lbt::KeyPath const &path)
{
    static TableRootCompute root;
    static mpt::lbt::LbtCompute<AccountValueHasher> account;
    static mpt::lbt::LbtCompute<PageValueHasher> storage;
    auto const pos = state_position(m);
    if (pos.level == StateLevel::table_root) {
        return root;
    }
    auto const key = path.view(pos.key_start, m.depth);
    if (pos.level == StateLevel::account) {
        account.bind_key(key);
        return account;
    }
    storage.bind_key(key);
    return storage;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <class Base>
mpt::state_machine_kind LbtMachine<Base>::kind() const
{
    return mpt::state_machine_kind::lbt_binary;
}

template <class Base>
std::unique_ptr<mpt::StateMachine> LbtMachine<Base>::clone() const
{
    return std::make_unique<LbtMachine>(*this);
}

template <class Base>
void LbtMachine<Base>::down(unsigned char const nibble)
{
    path_.set(this->depth, nibble);
    Base::down(nibble);
}

template <class Base>
void LbtMachine<Base>::down(mpt::NibblesView const path)
{
    path_.set(this->depth, path);
    Base::down(path);
}

template <class Base>
mpt::NibblesView LbtMachine<Base>::state_key_prefix() const
{
    return path_.view(state_position(*this).key_start, this->depth);
}

template <class Base>
mpt::Compute &LbtMachine<Base>::get_compute() const
{
    if (this->table != MachineBase::TableType::State) {
        return MachineBase::get_compute();
    }
    return state_compute(*this, path_);
}

template struct LbtMachine<InMemoryMachine>;
template struct LbtMachine<OnDiskMachine>;

void register_lbt_state_machines()
{
    mpt::register_state_machine(mpt::state_machine_kind::lbt_binary, [] {
        return std::make_unique<LbtOnDiskMachine>();
    });
}

MONAD_NAMESPACE_END
