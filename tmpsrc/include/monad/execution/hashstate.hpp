#pragma once

#include <silkworm/stagedsync/common.hpp>

namespace silkworm::stagedsync {

class MonadHashState final : public IStage {
  public:
    explicit MonadHashState(NodeSettings* node_settings)
        : IStage(db::stages::kHashStateKey, node_settings){};
    ~MonadHashState() override = default;
    StageResult forward(db::RWTxn& txn) final;

    std::vector<std::string> get_log_progress() final;

  private:
    //! \brief Store already processed addresses to avoid rehashing and multiple lookups
    //! \struct Address -> Address Hash -> Value
    using ChangedAddresses = absl::btree_map<evmc::address, std::pair<evmc::bytes32, Bytes>>;

    //! \brief Transforms PlainState into HashedAccounts and HashedStorage respectively in one single read pass over
    //! PlainState \remarks To be used only if this is very first time HashState stage runs forward (i.e. forwarding
    //! from 0)
    StageResult hash_from_plainstate(db::RWTxn& txn);

    //! \brief Transforms PlainCodeHash into HashedCodeHash in one single read pass over PlainCodeHash
    //! \remarks To be used only if this is very first time HashState stage runs forward (i.e. forwarding from 0)
    StageResult hash_from_plaincode(db::RWTxn& txn);

    //! \brief Detects account changes from AccountChangeSet and hashes the changed keys
    //! \remarks Though it could be used for initial sync only is way slower and builds an index of changed accounts.
    StageResult hash_from_account_changeset(db::RWTxn& txn, BlockNum curr_block_num);

    //! \brief Detects storage changes from StorageChangeSet and hashes the changed keys
    //! \remarks Though it could be used for initial sync only is way slower and builds an index of changed storage
    //! locations.
    StageResult hash_from_storage_changeset(db::RWTxn& txn, BlockNum curr_block_num);

    // tzhi: should we ever care abou unwinding?
    //! \brief Detects account changes from AccountChangeSet and reverts hashed states
    StageResult unwind_from_account_changeset(db::RWTxn& txn, BlockNum previous_progress, BlockNum to);

    //! \brief Detects storage changes from StorageChangeSet and reverts hashed states
    StageResult unwind_from_storage_changeset(db::RWTxn& txn, BlockNum previous_progress, BlockNum to);

    //! \brief Writes to db the changes collected from account changeset scan either in forward or unwind mode
    StageResult write_changes_from_changed_addresses(db::RWTxn& txn, const ChangedAddresses& changed_addresses);

    //! \brief Writes to db the changes collected from storage changeset scan either in forward or unwind mode
    StageResult write_changes_from_changed_storage(db::RWTxn& txn, db::StorageChanges& storage_changes,
                                                   const absl::btree_map<evmc::address, evmc::bytes32>& hashed_addresses);
};

} // namespace silkworm::stagedsync

