// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// monad-domain derives one private domain's blocks from the finalized chain
// of an L1 node, reading the node's triedb read-only, into a block store of
// its own, and executes them into a triedb of the domain's own. See
// PROTOCOL.md in category-labs/monad-domains.

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/cli/help_formatter.hpp>
#include <category/core/config.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/log.hpp>
#include <category/execution/domain/block_store.hpp>
#include <category/execution/domain/chain_id.hpp>
#include <category/execution/domain/deriver.hpp>
#include <category/execution/domain/domain_block.hpp>
#include <category/execution/domain/executor.hpp>
#include <category/execution/domain/hpke.hpp>
#include <category/execution/domain/l1_source.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/log_level_map.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/state_machine_init.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/chain/chain_factory.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/db/state_machine_init.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_error.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <CLI/CLI.hpp>
#include <nlohmann/json.hpp>
#include <quill/std/FilesystemPath.h>

#include <chrono>
#include <csignal>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <thread>
#include <tuple>
#include <unordered_map>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// How often to look for a newly finalized L1 block once caught up.
constexpr auto POLL_INTERVAL = std::chrono::milliseconds{20};
// Threads and fibers of the priority pool domain blocks execute on.
constexpr unsigned EXECUTION_THREADS = 4;
constexpr unsigned EXECUTION_FIBERS = 256;

sig_atomic_t volatile stop;

void signal_handler(int)
{
    stop = 1;
}

std::string
validate_address(std::string const &value, bool const require_nonzero)
{
    std::string_view hex{value};
    skip_optional_hex_prefix(hex);
    auto const address = from_hex<Address>(value);
    if (hex.size() != sizeof(Address) * 2 || !address.has_value()) {
        return "address must contain exactly 20 bytes of hexadecimal";
    }
    if (require_nonzero && *address == Address{}) {
        return "address must be nonzero";
    }
    return {};
}

std::string hex(byte_string_view const bytes)
{
    return "0x" + to_hex(bytes);
}

// Prints the store's blocks as JSON lines, from genesis to its tip.
int dump_blocks(domain::DomainBlockStore const &store)
{
    if (!store.tip().has_value()) {
        return EXIT_SUCCESS;
    }
    for (uint64_t number = 0; number <= store.tip()->header.number; ++number) {
        auto const block = store.get(number);
        MONAD_ASSERT(block.has_value());
        auto const &header = block->header;
        nlohmann::json transactions = nlohmann::json::array();
        for (auto const &tx : block->transactions) {
            auto const sender = recover_sender(tx);
            transactions.push_back(
                {{"encoded", hex(rlp::encode_transaction(tx))},
                 {"sender",
                  sender.has_value()
                      ? nlohmann::json(hex(to_byte_string_view(sender->bytes)))
                      : nlohmann::json(nullptr)}});
        }
        nlohmann::json json{
            {"parent_id", hex(to_byte_string_view(header.parent_id.bytes))},
            {"number", header.number},
            {"l1_block_number", header.l1_block_number},
            {"l1_block_hash",
             hex(to_byte_string_view(header.l1_block_hash.bytes))},
            {"timestamp", header.timestamp},
            {"mix_hash", hex(to_byte_string_view(header.mix_hash.bytes))},
            {"gas_limit", header.gas_limit},
            {"base_fee_per_gas", to_string(header.base_fee_per_gas, 10)},
            {"transactions_root",
             hex(to_byte_string_view(header.transactions_root.bytes))},
            {"transactions", std::move(transactions)}};
        if (header.slot_number.has_value()) {
            json["slot_number"] = *header.slot_number;
        }
        std::cout << json.dump() << '\n';
    }
    return EXIT_SUCCESS;
}

MONAD_ANONYMOUS_NAMESPACE_END

using namespace monad;
namespace fs = std::filesystem;

int main(int const argc, char const *argv[])
try {
    CLI::App cli{
        "Derive one private domain's blocks from the finalized chain of an L1 "
        "node, reading its triedb read-only, into a block store, and with "
        "--domain-db execute them.",
        "monad-domain"};
    monad::cli::HelpFormatter{GIT_COMMIT_HASH}.install(cli);

    monad_chain_config chain_config{};
    fs::path l1_db_path;
    std::tuple<uint64_t, std::string, fs::path> domain;
    std::string hub_hex;
    fs::path store_dir;
    std::optional<uint64_t> start_l1_block;
    fs::path domain_db_path;
    bool dump = false;
    auto log_level = quill::LogLevel::Info;

    std::unordered_map<std::string, monad_chain_config> const CHAIN_CONFIG_MAP =
        {{"monad_devnet", CHAIN_CONFIG_MONAD_DEVNET},
         {"monad_testnet", CHAIN_CONFIG_MONAD_TESTNET},
         {"monad_mainnet", CHAIN_CONFIG_MONAD_MAINNET}};

    cli.add_option("--store", store_dir, "the domain's block store directory")
        ->required();
    auto *const dump_option = cli.add_flag(
        "--dump-blocks",
        dump,
        "print the store's blocks as JSON lines, from genesis to its tip, and "
        "exit");
    auto *const chain_option =
        cli.add_option("--chain", chain_config, "the L1 chain config")
            ->transform(
                CLI::CheckedTransformer(CHAIN_CONFIG_MAP, CLI::ignore_case));
    auto *const l1_db_option =
        cli.add_option("--l1-db", l1_db_path, "the L1 node's triedb");
    auto *const domain_option =
        cli.add_option(
               "--domain",
               domain,
               "the domain to derive, its spoke address and its HPKE "
               "receiver key")
            ->type_name("<CHAIN_ID> <SPOKE_ADDRESS> <PRIVATE_KEY_PEM_PATH>");
    CLI::Validator spoke_address_validator{
        [](std::string &value) { return validate_address(value, true); }, ""};
    auto key_file_validator = CLI::ExistingFile;
    key_file_validator.description("").application_index(2);
    domain_option->check(spoke_address_validator.application_index(1))
        ->check(key_file_validator);
    auto *const hub_option =
        cli.add_option("--hub", hub_hex, "the L1 DomainHub address")
            ->type_name("ADDRESS")
            ->check([](std::string const &value) {
                return validate_address(value, true);
            });
    cli.add_option(
        "--start-l1-block",
        start_l1_block,
        "L1 block to start from on an empty store, at or before the domain's "
        "registration");
    cli.add_option(
        "--domain-db",
        domain_db_path,
        "the domain's own triedb, created once the domain's genesis is "
        "derived: with it, monad-domain also executes the domain's blocks");
    cli.add_option("--log-level", log_level, "level of logging")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    for (auto *const option :
         {chain_option, l1_db_option, domain_option, hub_option}) {
        option->excludes(dump_option);
    }

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::ParseError const &e) {
        return cli.exit(e);
    }

    init_root_logger(log_level);

    domain::DomainBlockStore store{store_dir};
    if (dump) {
        return dump_blocks(store);
    }

    for (auto const *const option :
         {chain_option, l1_db_option, domain_option, hub_option}) {
        if (option->count() == 0) {
            LOG_ERROR("{} is required", option->get_name());
            return EXIT_FAILURE;
        }
    }
    if (!store.l1_cursor().has_value() && !store.tip().has_value() &&
        !start_l1_block.has_value()) {
        LOG_ERROR("--start-l1-block is required on an empty store");
        return EXIT_FAILURE;
    }

    auto const &[domain_chain_id, spoke_hex, key_path] = domain;
    auto const chain = make_monad_chain(chain_config);
    auto const network_chain_id = chain->get_chain_id();
    auto const domain_id = domain::domain_from_chain_id(
        uint256_t{domain_chain_id}, network_chain_id);
    if (domain_id.has_error() || !domain_id.value().has_value()) {
        LOG_ERROR(
            "domain chain ID {} must differ from and end with L1 chain ID {}",
            domain_chain_id,
            to_string(network_chain_id, 10));
        return EXIT_FAILURE;
    }
    auto key = domain::PrivateDomainKey::load(key_path);
    if (key.has_error()) {
        LOG_ERROR(
            "cannot load the domain key {}: {}",
            key_path,
            key.assume_error().message().c_str());
        return EXIT_FAILURE;
    }
    Address const spoke = *from_hex<Address>(spoke_hex);
    Address const hub = *from_hex<Address>(hub_hex);

    mpt::AsyncIOContext io_ctx{
        mpt::ReadOnlyOnDiskDbConfig{.dbname_path = l1_db_path}};
    mpt::Db const l1_db{io_ctx};
    domain::TrieDbL1Source const l1{l1_db};
    domain::PrivateDomainDeriver deriver{
        l1,
        store,
        key.value(),
        domain_chain_id,
        spoke,
        hub,
        start_l1_block.value_or(0)};
    LOG_INFO(
        "deriving private domain {} from DomainHub {}, from L1 block {}",
        domain_chain_id,
        hub_hex,
        deriver.next_l1_block());

    signal(SIGINT, signal_handler);
    signal(SIGTERM, signal_handler);
    // The domain db is created for the revision of the domain's genesis, so
    // that it has the encoding the blocks commit with.
    std::optional<fiber::PriorityPool> priority_pool;
    std::optional<vm::VM> vm;
    std::optional<mpt::Db> domain_db;
    std::optional<domain::PrivateDomainExecutor> executor;
    // Opened as the L1 node opens its db, with compaction and a rewind of
    // anything committed past the last finalized block, but without an SQPOLL
    // kernel thread, which would spin on a CPU beside the L1 node's.
    auto const domain_db_config = [&](bool const append) {
        return mpt::OnDiskDbConfig{
            .append = append,
            .compaction = true,
            .rewind_to_latest_finalized = true,
            .sq_thread_cpu = std::nullopt,
            .dbname_path = domain_db_path};
    };
    auto const open_executor = [&] {
        if (fs::exists(domain_db_path)) {
            register_ethereum_state_machines();
            register_monad_state_machines();
            domain_db.emplace(domain_db_config(true));
        }
        else {
            auto const genesis = store.get(0);
            if (!genesis.has_value()) {
                return;
            }
            std::unique_ptr<mpt::StateMachine> machine;
            if (mip_8_active(
                    chain->get_monad_revision(genesis->header.timestamp))) {
                machine = std::make_unique<MonadOnDiskMachine>();
            }
            else {
                machine = std::make_unique<OnDiskMachine>();
            }
            domain_db.emplace(std::move(machine), domain_db_config(false));
        }
        priority_pool.emplace(EXECUTION_THREADS, EXECUTION_FIBERS);
        vm.emplace();
        executor.emplace(
            *chain, domain_chain_id, store, *domain_db, *vm, *priority_pool);
        LOG_INFO(
            "executing private domain {} into {}, from domain block {}",
            domain_chain_id,
            domain_db_path,
            executor->next_block());
    };

    while (!stop) {
        auto const tip = store.tip().has_value()
                             ? std::optional{store.tip()->header.number}
                             : std::nullopt;
        auto const derived = deriver.derive_next();
        if (derived.has_error()) {
            if (derived.assume_error() ==
                mpt::DbError::version_no_longer_exist) {
                LOG_ERROR(
                    "L1 block {} has left the L1 db's history, which starts "
                    "at {}: this store can no longer catch up from it",
                    deriver.next_l1_block(),
                    l1_db.get_earliest_version());
            }
            else {
                LOG_ERROR(
                    "deriving L1 block {} failed: {}",
                    deriver.next_l1_block(),
                    derived.assume_error().message().c_str());
            }
            return EXIT_FAILURE;
        }
        if (store.tip().has_value() &&
            (!tip.has_value() || store.tip()->header.number != *tip)) {
            LOG_INFO(
                "domain block {} from L1 block {}, {} transactions",
                store.tip()->header.number,
                store.tip()->header.l1_block_number,
                store.tip()->transactions.size());
        }

        bool executed = false;
        if (!domain_db_path.empty() && !executor.has_value()) {
            open_executor();
        }
        if (executor.has_value()) {
            auto const result = executor->execute_next();
            if (result.has_error()) {
                LOG_ERROR(
                    "executing domain block {} failed: {}",
                    executor->next_block(),
                    result.assume_error().message().c_str());
                return EXIT_FAILURE;
            }
            executed = result.value();
            if (executed) {
                LOG_INFO(
                    "executed domain block {}", executor->next_block() - 1);
            }
        }
        if (!derived.value() && !executed) {
            std::this_thread::sleep_for(POLL_INTERVAL);
        }
    }
    LOG_INFO("stopped at L1 block {}", deriver.next_l1_block());
    return EXIT_SUCCESS;
}
catch (std::exception const &e) {
    std::cerr << e.what() << '\n';
    return EXIT_FAILURE;
}
