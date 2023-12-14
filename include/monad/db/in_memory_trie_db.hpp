#pragma once

#include <monad/core/bytes.hpp>
#include <monad/db/config.hpp>
#include <monad/db/db.hpp>
#include <monad/mpt/compute.hpp>
#include <monad/mpt/trie.hpp>

#include <ankerl/unordered_dense.h>
#include <nlohmann/json.hpp>

#include <list>

MONAD_DB_NAMESPACE_BEGIN

struct Compute
{
    static byte_string compute(mpt::Node const &);
};

using MerkleCompute = mpt::MerkleComputeBase<Compute>;

class EmptyStateMachine final : public mpt::StateMachine
{
private:
    MerkleCompute compute_;

public:
    virtual std::unique_ptr<StateMachine> clone() const override;
    virtual void down(unsigned char nibble) override;
    virtual void up(size_t) override;
    virtual mpt::Compute &get_compute() override;
    virtual mpt::CacheOption get_cache_option() const override;
};

class InMemoryTrieDB final : public Db
{
private:
    mpt::Node::UniquePtr root_;
    std::list<mpt::Update> update_allocator_;
    std::list<byte_string> byte_string_allocator_;
    ankerl::unordered_dense::segmented_map<bytes32_t, byte_string> code_;

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
