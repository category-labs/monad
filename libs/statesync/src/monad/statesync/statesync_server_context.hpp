#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/db/db.hpp>
#include <monad/mpt/db.hpp>

#include <array>
#include <deque>
#include <functional>
#include <mutex>
#include <vector>

MONAD_NAMESPACE_BEGIN

inline constexpr size_t MAX_ENTRIES = 43'200;
inline constexpr size_t MAX_DELETIONS = 2'000'000;

struct Deletion
{
    Address address;
    std::optional<bytes32_t> key;

    friend bool operator==(Deletion const &, Deletion const &) = default;
};

static_assert(sizeof(Deletion) == 53);
static_assert(alignof(Deletion) == 1);

struct FinalizedDeletionsEntry
{
    std::mutex mutex{};
    uint64_t block_number{mpt::INVALID_BLOCK_ID};
    size_t idx{0};
    size_t size{0};
};

static_assert(sizeof(FinalizedDeletionsEntry) == 64);
static_assert(alignof(FinalizedDeletionsEntry) == 8);

class FinalizedDeletions
{
    uint64_t start_block_number_{mpt::INVALID_BLOCK_ID};
    uint64_t end_block_number_{mpt::INVALID_BLOCK_ID};
    std::array<FinalizedDeletionsEntry, MAX_ENTRIES> entries_{};
    std::array<Deletion, MAX_DELETIONS> deletions_{};
    size_t free_start_{0};
    size_t free_end_{MAX_DELETIONS};

    void
    set_entry(uint64_t i, uint64_t block_number, std::vector<Deletion> const &);
    void clear_entry(uint64_t i);

public:
    bool for_each(uint64_t block_number, std::function<void(Deletion const &)>);
    void write(uint64_t block_number, std::vector<Deletion> const &);
};

static_assert(sizeof(FinalizedDeletions) == 108764832);
static_assert(alignof(FinalizedDeletions) == 8);

struct ProposedDeletions
{
    uint64_t block_number;
    uint64_t round;
    std::vector<Deletion> deletions;
};

static_assert(sizeof(ProposedDeletions) == 40);
static_assert(alignof(ProposedDeletions) == 8);

struct CallFrame;
class TrieDb;

MONAD_NAMESPACE_END

struct monad_statesync_server_context final : public monad::Db
{
    monad::TrieDb &rw;
    monad::mpt::Db *ro;
    std::deque<monad::ProposedDeletions> proposals;
    monad::FinalizedDeletions deletions;

    explicit monad_statesync_server_context(monad::TrieDb &rw);

    virtual std::optional<monad::Account>
    read_account(monad::Address const &addr) override;

    virtual monad::bytes32_t read_storage(
        monad::Address const &addr, monad::Incarnation,
        monad::bytes32_t const &key) override;

    virtual std::shared_ptr<monad::CodeAnalysis>
    read_code(monad::bytes32_t const &hash) override;

    virtual monad::BlockHeader read_eth_header() override;

    virtual monad::bytes32_t state_root() override;

    virtual monad::bytes32_t receipts_root() override;

    virtual monad::bytes32_t transactions_root() override;

    virtual std::optional<monad::bytes32_t> withdrawals_root() override;

    virtual void set_block_and_round(
        uint64_t block_number,
        std::optional<uint64_t> round_number = std::nullopt) override;
    virtual void
    finalize(uint64_t block_number, uint64_t round_number) override;
    virtual void update_verified_block(uint64_t) override;

    virtual void commit(
        monad::StateDeltas const &state_deltas, monad::Code const &code,
        monad::MonadConsensusBlockHeader const &,
        std::vector<monad::Receipt> const &receipts = {},
        std::vector<std::vector<monad::CallFrame>> const & = {},
        std::vector<monad::Address> const & = {},
        std::vector<monad::Transaction> const &transactions = {},
        std::vector<monad::BlockHeader> const &ommers = {},
        std::optional<std::vector<monad::Withdrawal>> const & =
            std::nullopt) override;
};
