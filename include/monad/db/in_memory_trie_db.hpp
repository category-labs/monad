#pragma once

#include <monad/core/bytes.hpp>
#include <monad/db/config.hpp>
#include <monad/db/db.hpp>
#include <monad/mpt/compute.hpp>
#include <monad/mpt/trie.hpp>

#include <nlohmann/json.hpp>

#include <list>

MONAD_DB_NAMESPACE_BEGIN

class InMemoryTrieDB final : public Db
{
private:
    mpt::Node::UniquePtr root_;
    std::list<mpt::Update> update_alloc_;
    std::list<byte_string> bytes_alloc_;

public:
    InMemoryTrieDB() = default;
    InMemoryTrieDB(nlohmann::json const &);

    virtual std::optional<Account> read_account(Address const &) const override;
    virtual bytes32_t
    read_storage(Address const &, bytes32_t const &key) const override;
    virtual byte_string read_code(bytes32_t const &hash) const override;
    virtual void commit(StateDeltas const &, Code const &) override;
    virtual void create_and_prune_block_history(uint64_t) const override;

    bytes32_t state_root() const;
    nlohmann::json to_json() const;
};

MONAD_DB_NAMESPACE_END
