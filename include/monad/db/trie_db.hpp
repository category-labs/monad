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

MONAD_DB_NAMESPACE_BEGIN

class TrieDb final : public ::monad::Db
{
private:
    ::monad::mpt::Db db_;
    std::list<mpt::Update> update_alloc_;
    std::list<byte_string> bytes_alloc_;

    struct Machine final : public mpt::StateMachine
    {
        uint8_t depth = 0;
        bool is_merkle = false;

        virtual std::unique_ptr<mpt::StateMachine> clone() const override;
        virtual void down(unsigned char const nibble) override;
        virtual void up(size_t const n) override;
        virtual mpt::Compute &get_compute() override;
        virtual bool cache() const override;
    } machine_;

    static_assert(sizeof(Machine) == 16);

public:
    TrieDb(mpt::DbOptions const &);
    TrieDb(mpt::DbOptions const &, std::istream &, size_t batch_size = 1048576);

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
