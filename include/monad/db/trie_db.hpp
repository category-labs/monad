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
};

//! with 12-nibble block num and 1-nibble prefix
struct OnDiskMachine final : public Machine
{
    using Machine::depth;
    using Machine::is_merkle;

    static constexpr auto block_num_len = 0;
    static constexpr auto prefix_len = 1;
    static constexpr auto cache_depth = block_num_len + prefix_len + 5;
    static constexpr auto max_depth = block_num_len + prefix_len + 64 + 64;

    virtual std::unique_ptr<mpt::StateMachine> clone() const override;
    virtual void down(unsigned char const nibble) override;
    virtual void up(size_t const n) override;
    virtual mpt::Compute &get_compute() const override;
    virtual bool cache() const override;
};

class TrieDb final : public ::monad::Db

{
private:
    std::unique_ptr<Machine> machine_;
    ::monad::mpt::Db db_;
    std::list<mpt::Update> update_alloc_;
    std::list<byte_string> bytes_alloc_;
    bool insert_code_;

public:
    TrieDb(mpt::DbOptions const &, bool insert_code = true);
    // parse from json
    TrieDb(
        mpt::DbOptions const &, std::istream &, bool insert_code = true,
        size_t batch_size = 262144);
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
};

MONAD_DB_NAMESPACE_END
