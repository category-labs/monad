#pragma once

#include <monad/db/block_db.hpp>

#include <silkworm/etl/collector.hpp>
#include <silkworm/stagedsync/common.hpp>
#include <silkworm/stagedsync/stage_interhashes/trie_loader.hpp>
#include <silkworm/trie/hash_builder.hpp>
#include <silkworm/trie/prefix_set.hpp>

namespace silkworm::stagedsync {

class MonadInterHashes final : public IStage {
  public:
    explicit MonadInterHashes(NodeSettings* node_settings)
        : IStage(db::stages::kIntermediateHashesKey, node_settings),
          block_db_{node_settings->data_directory->block_db().path()} {};
    ~MonadInterHashes() override = default;
    StageResult forward(db::RWTxn& txn) final;
    std::vector<std::string> get_log_progress() final;

  private:
    monad::BlockDb const block_db_;

    //! \brief Resets all fields related to log progress tracking
    void reset_log_progress();

    //! \brief See Erigon (p *HashPromoter) Promote
    trie::PrefixSet collect_account_changes(db::RWTxn& txn, BlockNum curr_block_num,
                                            absl::btree_map<evmc::address, ethash_hash256>& hashed_addresses);

    //! \brief See Erigon (p *HashPromoter) Promote
    trie::PrefixSet collect_storage_changes(db::RWTxn& txn, BlockNum curr_block_num,
                                            absl::btree_map<evmc::address, ethash_hash256>& hashed_addresses);

    //! \brief Erigon's IncrementIntermediateHashes
    //! \remarks might throw
    //! \return the state root
    [[nodiscard]] StageResult increment_intermediate_hashes(db::RWTxn& txn, BlockNum curr_block_num,
                                                            const evmc::bytes32* expected_root = nullptr);

    //! \brief Persists in TrieAccount and TrieStorage the collected nodes (and respective deletions if any)
    void flush_collected_nodes(db::RWTxn& txn);

    std::unique_ptr<trie::TrieLoader> trie_loader_;      // The loader which (re)builds the trees
    std::unique_ptr<etl::Collector> account_collector_;  // To accumulate new records for kTrieOfAccounts
    std::unique_ptr<etl::Collector> storage_collector_;  // To accumulate new records for kTrieOfStorage
    std::unique_ptr<etl::Collector> loading_collector_;  // Effectively the current collector undergoing load (for log)
};

}  // namespace silkworm::stagedsync