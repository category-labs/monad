#include <monad/async/util.hpp>
#include <monad/chain/monad_devnet.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.h>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/small_prng.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/switch_evmc_revision.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>
#include <fuzzer/FuzzedDataProvider.h>
#include <intx/intx.hpp>
#include <quill/Quill.h>
#include <secp256k1.h>
#include <secp256k1_recovery.h>

#include <algorithm>
#include <iterator>
#include <list>
#include <memory>
#include <optional>
#include <set>

using namespace monad;

namespace
{
    constexpr uint64_t GAS_LIMIT = 60'000;
    constexpr uint256_t BASE_FEE_PER_GAS = 1;
}

static auto ctx = []() {
    std::unique_ptr<secp256k1_context, decltype(&secp256k1_context_destroy)>
        context(
            secp256k1_context_create(
                SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY),
            secp256k1_context_destroy);
    return context;
}();

std::filesystem::path tmp_dbname()
{
    std::filesystem::path dbname(
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_fuzz_execution_XXXXXX");
    int const fd = ::mkstemp((char *)dbname.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(
        -1 != ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
    ::close(fd);
    char const *const path = dbname.c_str();
    OnDiskMachine machine;
    mpt::Db const db{
        machine, mpt::OnDiskDbConfig{.append = false, .dbname_paths = {path}}};
    return dbname;
}

class Wallet
{
public:
    bytes32_t privkey_;
    Address address_;

    uint64_t nonce;
    uint256_t balance;

public:
    Wallet(bytes32_t const &privkey)
        : privkey_{privkey}
        , nonce{0}
        , balance{0}
    {
        secp256k1_pubkey pubkey{};
        if (!secp256k1_ec_pubkey_create(ctx.get(), &pubkey, privkey_.bytes)) {
            MONAD_ABORT("Could not generate wallet");
        }

        unsigned char serialized_pubkey[65];
        size_t pubkey_len = sizeof(serialized_pubkey);
        if (!secp256k1_ec_pubkey_serialize(
                ctx.get(),
                serialized_pubkey,
                &pubkey_len,
                &pubkey,
                SECP256K1_EC_UNCOMPRESSED)) {
            MONAD_ABORT("Could not serialize pubkey");
        }
        MONAD_ASSERT(serialized_pubkey[0] == 4);
        auto const hash =
            keccak256(byte_string_view{serialized_pubkey + 1, 64});
        std::copy_n(hash.bytes + 12, sizeof(Address), address_.bytes);
    }

    Address const &address() const
    {
        return address_;
    }

    void sign(
        bytes32_t const &msg_hash, uint256_t &r, uint256_t &s,
        bool &odd_y_parity) const
    {
        secp256k1_ecdsa_recoverable_signature sig{};
        if (!secp256k1_ecdsa_sign_recoverable(
                ctx.get(),
                &sig,
                msg_hash.bytes,
                privkey_.bytes,
                nullptr,
                nullptr)) {
            MONAD_ABORT("Could not sign mesasge");
        }

        unsigned char compact_sig[64];
        int recid{};
        if (!secp256k1_ecdsa_recoverable_signature_serialize_compact(
                ctx.get(), compact_sig, &recid, &sig)) {
            MONAD_ABORT("Could not get signature parity");
        }

        unsigned char r2[32];
        unsigned char s2[32];
        std::copy_n(compact_sig, 32, r2);
        std::copy_n(compact_sig + 32, 32, s2);
        r = intx::be::load<uint256_t>(r2);
        s = intx::be::load<uint256_t>(s2);
        odd_y_parity = static_cast<bool>(recid);
    }

    void add_to_balance(uint256_t const &amount)
    {
        balance += amount;
    }

    void subtract_from_balance(uint256_t const &amount)
    {
        if (MONAD_UNLIKELY(balance < amount)) {
            MONAD_ABORT("fuzzer logic error")
        }
        balance -= amount;
    }

    void increment_nonce()
    {
        ++nonce;
    }

    uint64_t get_nonce() const
    {
        return nonce;
    }

    uint256_t get_balance() const
    {
        return balance;
    }
};

using ProposalPayload = std::pair<BlockHeader, std::vector<Wallet>>;

struct Proposal;

struct Proposal
{
    ProposalPayload payload;
    std::list<Proposal> children;
};

std::pair<Block, std::vector<Wallet>> generate_proposal(
    FuzzedDataProvider &provider, ProposalPayload const &parent,
    uint64_t const round_lower_bound, Chain const &chain)
{
    Block block;
    std::vector<Wallet> wallets = parent.second;

    auto &header = block.header;

    header.round =
        round_lower_bound + provider.ConsumeIntegralInRange<uint64_t>(0, 100);
    header.parent_round = parent.first.round;
    header.number = parent.first.number + 1;

    header.difficulty = uint256_t{0};
    header.gas_limit = GAS_LIMIT;
    provider.ConsumeData(
        header.bft_block_id.bytes, sizeof(header.bft_block_id));
    header.beneficiary = wallets[provider.ConsumeIntegralInRange<uint64_t>(
                                     0, wallets.size() - 1)]
                             .address();
    header.timestamp = parent.first.timestamp +
                       provider.ConsumeIntegralInRange<uint64_t>(1, 1000);
    header.base_fee_per_gas = BASE_FEE_PER_GAS;
    provider.ConsumeData(header.prev_randao.bytes, sizeof(header.prev_randao));

    block.withdrawals.emplace(std::vector<Withdrawal>{});

    auto const num_txns = provider.ConsumeIntegralInRange<uint64_t>(0, 5);
    for (uint64_t i = 0; i < num_txns; ++i) {
        auto const fi =
            provider.ConsumeIntegralInRange<uint64_t>(0, wallets.size() - 1);
        auto const ti =
            provider.ConsumeIntegralInRange<uint64_t>(0, wallets.size() - 1);
        auto &from = wallets[fi];
        auto &to = wallets[ti];

        constexpr uint256_t amount = 10;
        Transaction tx{
            .sc = SignatureAndChain{.chain_id = chain.get_chain_id()},
            .nonce = from.get_nonce(),
            .max_fee_per_gas = BASE_FEE_PER_GAS,
            .gas_limit = GAS_LIMIT,
            .value = amount,
            .to = to.address(),
            .type = TransactionType::legacy,
            .data = byte_string{}};
        auto const gas_cost = [&] -> uint256_t {
            auto const rev =
                chain.get_revision(block.header.number, block.header.timestamp);
            SWITCH_EVMC_REVISION(intrinsic_gas, tx);
            return UINT256_MAX;
        }();
        from.subtract_from_balance(gas_cost + amount);
        from.increment_nonce();
        to.add_to_balance(amount);

        auto const hash = keccak256(rlp::encode_transaction_for_signing(tx));
        from.sign(
            std::bit_cast<bytes32_t>(hash),
            tx.sc.r,
            tx.sc.s,
            tx.sc.odd_y_parity);
        block.transactions.emplace_back(std::move(tx));
    }

    return std::make_pair(block, wallets);
}

ProposalPayload const &finalize_proposal(
    TrieDb &tdb, FuzzedDataProvider &provider, BlockHashChain &chain,
    std::list<Proposal> const &lst)
{
    size_t finalize_idx =
        provider.ConsumeIntegralInRange<size_t>(0, lst.size() - 1);
    auto it = lst.begin();
    std::advance(it, finalize_idx);

    auto const &[hdr, wallets] = it->payload;
    tdb.finalize(hdr.number, hdr.round);
    chain.finalize(hdr.round);

    tdb.set_block_and_round(hdr.number);
    for (auto const &w : wallets) {
        auto const account = tdb.read_account(w.address());
        MONAD_ASSERT(account.has_value());

        if (MONAD_UNLIKELY(w.get_nonce() != account.value().nonce)) {
            MONAD_ABORT_PRINTF(
                "Bad nonce: Expected %lu, got %lu",
                w.get_nonce(),
                account.value().nonce);
        }
        if (MONAD_UNLIKELY(w.get_balance() != account.value().balance)) {
            MONAD_ABORT_PRINTF(
                "Bad balance. Expected %s, got %s",
                intx::to_string(w.get_balance()).c_str(),
                intx::to_string(account.value().balance).c_str());
        }
    }

    if (!it->children.empty()) {
        return finalize_proposal(tdb, provider, chain, it->children);
    }
    return it->payload;
}

class BlockFuzzer
{
    TrieDb &tdb_;
    FuzzedDataProvider &provider_;

    BlockHashBufferFinalized block_hash_buffer_;
    std::unique_ptr<BlockHashChain> block_hash_chain_;
    std::list<Proposal> proposals_tree_;
    std::vector<std::list<Proposal>::iterator> flat_proposals_;
    std::unique_ptr<Chain> chain_;
    ProposalPayload last_finalized_;
    uint64_t proposed_round_lower_bound_;
    fiber::PriorityPool priority_pool_;

    void execute_or_fail(Block &block)
    {
        if (auto const res = chain_->static_validate_header(block.header);
            res.has_error()) {
            MONAD_ABORT_PRINTF(
                "Error validating header(%lu, %lu): %s",
                block.header.number,
                block.header.round,
                res.error().message().c_str());
        }

        evmc_revision const rev =
            chain_->get_revision(block.header.number, block.header.timestamp);

        if (auto const res = static_validate_block(rev, block);
            res.has_error()) {
            MONAD_ABORT_PRINTF(
                "Error validating block(%lu, %lu): %s",
                block.header.number,
                block.header.round,
                res.error().message().c_str());
        }

        tdb_.set_block_and_round(
            block.header.number - 1, block.header.parent_round);

        auto const &block_hash_buffer =
            block_hash_chain_->find_chain(block.header.parent_round);
        BlockState block_state{tdb_};

        auto const results = execute_block(
            *chain_,
            rev,
            block,
            block_state,
            block_hash_buffer,
            priority_pool_);
        if (results.has_error()) {
            MONAD_ABORT_PRINTF(
                "Failed executing block(%lu, %lu): %s",
                block.header.number,
                block.header.round,
                results.error().message().c_str());
        }
        std::vector<Receipt> receipts(results.value().size());

        std::vector<std::vector<CallFrame>> call_frames(results.value().size());
        for (unsigned i = 0; i < results.value().size(); ++i) {
            auto &result = results.value()[i];
            receipts[i] = std::move(result.receipt);
            call_frames[i] = (std::move(result.call_frames));
        }

        block_state.commit(
            block.header,
            receipts,
            block.header.bft_block_id,
            call_frames,
            block.transactions,
            block.ommers,
            block.withdrawals,
            block.header.round);

        auto const db_eth_header = tdb_.read_eth_header();
        auto const encoded_header_mem = rlp::encode_block_header(block.header);
        auto const encoded_header_db = rlp::encode_block_header(db_eth_header);
        MONAD_ASSERT(encoded_header_mem == encoded_header_db);
        auto const eth_header_hash = to_bytes(keccak256(encoded_header_mem));
        block_hash_chain_->propose(
            eth_header_hash, block.header.round, block.header.parent_round);
    }

public:
    BlockFuzzer(TrieDb &tdb, FuzzedDataProvider &provider)
        : tdb_{tdb}
        , provider_{provider}
        , priority_pool_{1, 1}
    {

        BlockState bs{tdb_};
        State state{bs, Incarnation{0, 0}};
        std::set<bytes32_t> used_keys{};
        std::vector<Wallet> wallets;
        while (wallets.size() < 100) {
            bytes32_t key;
            provider_.ConsumeData(key.bytes, sizeof(bytes32_t));
            if (!used_keys.contains(key)) {
                used_keys.insert(key);
                auto &w = wallets.emplace_back(key);
                constexpr uint256_t b = 1'000'000'000'000;
                w.add_to_balance(b);
                state.add_to_balance(w.address(), b);
            }
        }
        bs.merge(state);
        tdb_.set_block_and_round(0, 0); // genesis
        bs.commit({}, {}, {}, {}, {}, {}, std::nullopt);
        auto const genesis_header = tdb_.read_eth_header();
        tdb_.finalize(0, 0);
        block_hash_buffer_.set(
            0, to_bytes(keccak256(rlp::encode_block_header(genesis_header))));
        last_finalized_.first = genesis_header;
        last_finalized_.second = wallets;
        block_hash_chain_ =
            std::make_unique<BlockHashChain>(block_hash_buffer_);
        proposed_round_lower_bound_ = 1;

        chain_ = std::make_unique<MonadDevnet>();
    }

    void propose()
    {
        if (proposals_tree_.empty()) {
            auto [block, wallet] = generate_proposal(
                provider_,
                last_finalized_,
                proposed_round_lower_bound_,
                *chain_);
            execute_or_fail(block);
            auto const &next = proposals_tree_.emplace_back(Proposal{
                .payload = std::make_pair(block.header, std::move(wallet)),
                .children = {}});
            flat_proposals_.emplace_back(std::prev(proposals_tree_.end()));
            proposed_round_lower_bound_ = next.payload.first.round + 1;
        }
        else {
            auto it = flat_proposals_[provider_.ConsumeIntegralInRange<size_t>(
                0, flat_proposals_.size() - 1)];
            auto [block, wallet] = generate_proposal(
                provider_, it->payload, proposed_round_lower_bound_, *chain_);
            execute_or_fail(block);
            auto const &next = it->children.emplace_back(Proposal{
                .payload = std::make_pair(block.header, std::move(wallet)),
                .children = {}});
            flat_proposals_.emplace_back(std::prev(it->children.end()));
            proposed_round_lower_bound_ = next.payload.first.round + 1;
        }
    }

    void finalize()
    {
        if (!proposals_tree_.empty()) {
            last_finalized_ = finalize_proposal(
                tdb_, provider_, *block_hash_chain_, proposals_tree_);
            proposals_tree_.clear();
            flat_proposals_.clear();
        }
    }
};

struct __attribute__((packed)) FuzzParams
{
    uint16_t num_events;
    float proposal_prob;
    uint32_t seed;
};

extern "C" int LLVMFuzzerTestOneInput(uint8_t const *data, size_t size)
{
    if (size < sizeof(FuzzParams)) {
        return -1;
    }

    auto const params = unaligned_load<FuzzParams>(data);
    std::vector<uint32_t> data_source;
    data_source.resize(1ULL * 1024 * 1024 * 1024 / sizeof(uint32_t));
    small_prng rng{params.seed};
    std::generate(data_source.begin(), data_source.end(), rng);

    quill::start(false);
    quill::get_root_logger()->set_log_level(quill::LogLevel::Error);

    auto dbname = tmp_dbname();
    OnDiskMachine machine;
    mpt::Db db{
        machine, mpt::OnDiskDbConfig{.append = true, .dbname_paths = {dbname}}};
    TrieDb tdb{db};

    FuzzedDataProvider provider(
        reinterpret_cast<uint8_t const *>(data_source.data()),
        data_source.size() * sizeof(uint32_t));
    BlockFuzzer fuzzer(tdb, provider);

    for (uint16_t e = 0; e < params.num_events; ++e) {
        if (params.proposal_prob >= provider.ConsumeProbability<float>()) {
            fuzzer.propose();
        }
        else {
            fuzzer.finalize();
        }
    }
    fuzzer.finalize();

    return 0;
}
