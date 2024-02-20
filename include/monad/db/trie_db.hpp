#pragma once

#include <monad/core/bytes.hpp>
#include <monad/db/config.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/mpt/compute.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/state_machine.hpp>

#include <nlohmann/json.hpp>

#include <istream>
#include <list>
#include <memory>
#include <optional>

MONAD_DB_NAMESPACE_BEGIN

struct Machine : public mpt::StateMachine
{
    uint8_t depth = 0;
    bool is_merkle = false;
    static constexpr auto prefix_len = 1;
    static constexpr auto max_depth = mpt::BLOCK_NUM_NIBBLES_LEN + prefix_len +
                                      sizeof(bytes32_t) * 2 +
                                      sizeof(bytes32_t) * 2;

    virtual mpt::Compute &get_compute() const override;
    virtual void down(unsigned char const nibble) override;
    virtual void up(size_t const n) override;
};

struct InMemoryMachine final : public Machine
{
    virtual bool cache() const override;
    virtual bool compact() const override;
    virtual std::unique_ptr<StateMachine> clone() const override;
};

struct OnDiskMachine final : public Machine
{
    static constexpr auto cache_depth =
        mpt::BLOCK_NUM_NIBBLES_LEN + prefix_len + 5;

    virtual bool cache() const override;
    virtual bool compact() const override;
    virtual std::unique_ptr<StateMachine> clone() const override;
};

class TrieDb final : public ::monad::Db
{
private:
    std::unique_ptr<Machine> machine_;
    ::monad::mpt::Db db_;
    std::list<mpt::Update> update_alloc_;
    std::list<byte_string> bytes_alloc_;

public:
    TrieDb(std::optional<mpt::OnDiskDbConfig> const &);
    // parse from json
    TrieDb(
        std::optional<mpt::OnDiskDbConfig> const &, std::istream &,
        size_t batch_size = 262144);
    // parse from binary
    TrieDb(
        std::optional<mpt::OnDiskDbConfig> const &, std::istream &accounts,
        std::istream &code, size_t buf_size = 1ul << 31);

    virtual std::optional<Account> read_account(Address const &) override;
    virtual bytes32_t
    read_storage(Address const &, bytes32_t const &key) override;
    virtual std::shared_ptr<CodeAnalysis> read_code(bytes32_t const &) override;
    virtual void commit(StateDeltas const &, Code const &) override;
    virtual bytes32_t state_root() override;
    virtual void create_and_prune_block_history(uint64_t) const override;

    nlohmann::json to_json();
};

MONAD_DB_NAMESPACE_END
