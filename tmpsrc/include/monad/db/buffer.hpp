#pragma once

#include <cassert>
#include <optional>
#include <vector>

#include <absl/container/btree_map.h>
#include <absl/container/flat_hash_map.h>
#include <absl/container/flat_hash_set.h>

#include <monad/db/block_db.hpp>
#include <monad/db/state_db.hpp>

#include <silkworm/db/access_layer.hpp>
#include <silkworm/db/util.hpp>
#include <silkworm/state/state.hpp>
#include <silkworm/trie/hash_builder.hpp>
#include <silkworm/types/account.hpp>
#include <silkworm/types/block.hpp>
#include <silkworm/types/receipt.hpp>

namespace silkworm::db {

using ChangedAddresses = absl::btree_map<evmc::address, std::pair<evmc::bytes32, Bytes>>;

class MonadBuffer : public State {
  public:
    // txn must be valid (its handle != nullptr)
    explicit MonadBuffer(monad::BlockDb const& block_db, monad::StateDb& state_db, mdbx::txn& txn, std::optional<BlockNum> historical_block = std::nullopt)
        : block_db_{block_db},
          state_db_{state_db},
          txn_{txn},
          historical_block_{historical_block} {
        (void)state_db_;  // TODO
        assert(txn_);
    }

    /** @name Readers */
    ///@{

    [[nodiscard]] std::optional<Account> read_account(const evmc::address& address) const noexcept override;

    [[nodiscard]] ByteView read_code(const evmc::bytes32& code_hash) const noexcept override;

    [[nodiscard]] evmc::bytes32 read_storage(const evmc::address& address, uint64_t incarnation,
                                             const evmc::bytes32& location) const noexcept override;

    /** Previous non-zero incarnation of an account; 0 if none exists. */
    [[nodiscard]] uint64_t previous_incarnation(const evmc::address& address) const noexcept override;

    [[nodiscard]] std::optional<BlockHeader> read_header(uint64_t block_number,
                                                         const evmc::bytes32& block_hash) const noexcept override;

    [[nodiscard]] bool read_body(uint64_t block_number, const evmc::bytes32& block_hash,
                                 BlockBody& out) const noexcept override;

    [[nodiscard]] std::optional<intx::uint256> total_difficulty(
        uint64_t block_number, const evmc::bytes32& block_hash) const noexcept override;

    [[nodiscard]] evmc::bytes32 state_root_hash() const override;

    [[nodiscard]] uint64_t current_canonical_block() const override;

    [[nodiscard]] std::optional<evmc::bytes32> canonical_hash(uint64_t block_number) const override;

    ///@}

    void insert_block(const Block& block, const evmc::bytes32& hash) override;

    void canonize_block(uint64_t block_number, const evmc::bytes32& block_hash) override;

    void decanonize_block(uint64_t block_number) override;

    void insert_receipts(uint64_t block_number, const std::vector<Receipt>& receipts) override;

    /** @name State changes
     *  Change sets are backward changes of the state, i.e. account/storage values <em>at the beginning of a block</em>.
     */
    ///@{

    /** Mark the beginning of a new block.
     * Must be called prior to calling update_account/update_account_code/update_storage.
     */
    void begin_block(uint64_t block_number) override;

    void update_account(const evmc::address& address, std::optional<Account> initial,
                        std::optional<Account> current) override;

    void update_account_code(const evmc::address& address, uint64_t incarnation, const evmc::bytes32& code_hash,
                             ByteView code) override;

    void update_storage(const evmc::address& address, uint64_t incarnation, const evmc::bytes32& location,
                        const evmc::bytes32& initial, const evmc::bytes32& current) override;

    void unwind_state_changes(uint64_t block_number) override;

    ///@}

    /// Account (backward) changes per block
    [[nodiscard]] const absl::btree_map<uint64_t, AccountChanges>& account_changes() const {
        return block_account_changes_;
    }

    /// Storage (backward) changes per block
    [[nodiscard]] const absl::btree_map<uint64_t, StorageChanges>& storage_changes() const {
        return block_storage_changes_;
    }

    [[nodiscard]] const absl::btree_map<evmc::address, std::optional<Account>>& accounts_diff() const {
        return accounts_diff_;
    }

    [[nodiscard]] const StorageChanges& storage_diff() const {
        return storage_diff_;
    }

    void clear_diffs() {
        accounts_diff_.clear();
        storage_diff_.clear();
    }

    //! \brief Persists *all* accrued contents into db
    //! \remarks write_history_to_db is implicitly called
    void write_to_db();

    //! \brief Persists *history* accrued contents into db
    void write_history_to_db();

  private:
    //! \brief Persists *state* accrued contents into db
    void write_state_to_db();

    void write_hash_to_db();

    monad::BlockDb const& block_db_;
    monad::StateDb& state_db_;
    mdbx::txn& txn_;
    std::optional<uint64_t> historical_block_{};

    absl::btree_map<Bytes, BlockHeader> headers_{};
    absl::btree_map<Bytes, BlockBody> bodies_{};
    absl::btree_map<Bytes, intx::uint256> difficulty_{};

    // State

    mutable absl::btree_map<evmc::address, std::optional<Account>> accounts_;

    // address -> incarnation -> location -> value
    mutable absl::btree_map<evmc::address, absl::btree_map<uint64_t, absl::btree_map<evmc::bytes32, evmc::bytes32>>>
        storage_;

    // Diff
    mutable absl::btree_map<evmc::address, std::optional<Account>> accounts_diff_;
    mutable StorageChanges storage_diff_;

    absl::btree_map<evmc::address, uint64_t> incarnations_;
    absl::btree_map<evmc::bytes32, Bytes> hash_to_code_;
    absl::btree_map<Bytes, evmc::bytes32> storage_prefix_to_code_hash_;

    // History and changesets

    absl::btree_map<uint64_t, AccountChanges> block_account_changes_;  // per block
    absl::btree_map<uint64_t, StorageChanges> block_storage_changes_;  // per block
    absl::btree_map<Bytes, Bytes> receipts_;
    absl::btree_map<Bytes, Bytes> logs_;

    // Current block stuff
    uint64_t block_number_{0};
    absl::flat_hash_set<evmc::address> changed_storage_;
};

}  // namespace silkworm::db