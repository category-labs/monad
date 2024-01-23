#pragma once

#include <monad/core/bytes.hpp>
#include <monad/db/config.hpp>
#include <monad/db/db.hpp>
#include <monad/mpt/compute.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/db_options.hpp>
#include <monad/mpt/state_machine.hpp>

#include <nlohmann/json.hpp>

#include <istream>
#include <list>
#include <optional>

MONAD_DB_NAMESPACE_BEGIN

struct Machine : public mpt::StateMachine
{
    uint8_t depth = 0;
    bool is_merkle = false;
};

struct InMemoryMachine final : public Machine
{
    using Machine::depth;
    using Machine::is_merkle;

    virtual std::unique_ptr<mpt::StateMachine> clone() const override;
    virtual void down(unsigned char const nibble) override;
    virtual void up(size_t const n) override;
    virtual mpt::Compute &get_compute() const override;
    virtual bool cache() const override;
    virtual bool compact() const override;
};

struct OnDiskMachine final : public Machine
{
    using Machine::depth;
    using Machine::is_merkle;

    static constexpr auto prefix_len = 1;
    size_t block_num_len;
    size_t cache_depth;
    size_t max_depth;

    virtual std::unique_ptr<mpt::StateMachine> clone() const override;
    virtual void down(unsigned char const nibble) override;
    virtual void up(size_t const n) override;
    virtual mpt::Compute &get_compute() const override;
    virtual bool cache() const override;
    virtual bool compact() const override;

    OnDiskMachine(size_t block_num_len_ = 0)
        : block_num_len(block_num_len_)
        , cache_depth(block_num_len + prefix_len + 5)
        , max_depth(
              block_num_len + prefix_len + sizeof(bytes32_t) * 2 +
              sizeof(bytes32_t) * 2)
    {
    }
};

class TrieDb final : public ::monad::Db
{
private:
    std::unique_ptr<Machine> machine_;
    ::monad::mpt::Db db_;
    std::list<mpt::Update> update_alloc_;
    std::list<byte_string> bytes_alloc_;

public:
    bool insert_code;
    bool per_block;
    uint64_t block_id;

    TrieDb(
        mpt::DbOptions const &, bool insert_code = true, bool per_block = false,
        uint64_t block_id = 0);
    // parse from json
    TrieDb(
        mpt::DbOptions const &, std::istream &, bool insert_code = true,
        bool per_block = false, size_t batch_size = 262144,
        uint64_t block_id = 0);
    // parse from binary
    TrieDb(
        mpt::DbOptions const &, std::istream &accounts, std::istream &code,
        size_t buf_size = 1ul << 31);

    virtual std::optional<Account> read_account(Address const &) override;
    virtual bytes32_t
    read_storage(Address const &, bytes32_t const &key) override;
    virtual byte_string read_code(bytes32_t const &hash) override;
    virtual void commit(StateDeltas const &, Code const &) override;
    virtual void create_and_prune_block_history(uint64_t) const override;

    bytes32_t state_root();
    nlohmann::json to_json();

    ::monad::mpt::Db &db()
    {
        return db_;
    }

    void commit(mpt::UpdateList);

    void commit_multiple_blocks_from_json(std::istream &);
};

MONAD_DB_NAMESPACE_END
