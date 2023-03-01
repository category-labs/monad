#pragma once

#include <monad/db/block_db.hpp>

#include <monad/execution/stage.hpp>

#include <silkworm/etl/collector.hpp>
#include <silkworm/stagedsync/common.hpp>
#include <silkworm/stagedsync/stage_interhashes/trie_loader.hpp>
#include <silkworm/trie/hash_builder.hpp>
#include <silkworm/trie/prefix_set.hpp>

namespace silkworm::stagedsync {

class MonadInterHashes final : public Stage {
  public:
    explicit MonadInterHashes(NodeSettings* node_settings)
        : Stage(node_settings) {};
    ~MonadInterHashes() override = default;
    StageResult run(db::RWTxn& txn, monad::BlockDb const &block_db, db::MonadBuffer &buffer, silkworm::BlockNum block_num) final;

  private:
    //! \brief See Erigon (p *HashPromoter) Promote
    trie::PrefixSet collect_account_changes(db::RWTxn& txn, db::MonadBuffer &buffer, BlockNum curr_block_num, 
                                            absl::btree_map<evmc::address, ethash_hash256>& hashed_addresses);

    //! \brief See Erigon (p *HashPromoter) Promote
    trie::PrefixSet collect_storage_changes(db::RWTxn& txn, db::MonadBuffer &buffer, BlockNum curr_block_num, 
                                            absl::btree_map<evmc::address, ethash_hash256>& hashed_addresses);

    //! \brief Erigon's IncrementIntermediateHashes
    //! \remarks might throw
    //! \return the state root
    [[nodiscard]] StageResult increment_intermediate_hashes(db::RWTxn& txn, db::MonadBuffer &buffer, BlockNum curr_block_num,
                                                            const evmc::bytes32* expected_root = nullptr);

    //! \brief Persists in TrieAccount and TrieStorage the collected nodes (and respective deletions if any)
    void flush_collected_nodes(db::RWTxn& txn);

    std::unique_ptr<trie::TrieLoader> trie_loader_;      // The loader which (re)builds the trees
    std::unique_ptr<etl::Collector> account_collector_;  // To accumulate new records for kTrieOfAccounts
    std::unique_ptr<etl::Collector> storage_collector_;  // To accumulate new records for kTrieOfStorage
};

}  // namespace silkworm::stagedsync