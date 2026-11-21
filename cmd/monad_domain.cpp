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

// monad-domain derives one private domain's blocks from the finalized chain of
// an L1 node, reading the node's triedb read-only, and executes each block into
// the domain's own triedb. On start it resumes from the domain's last executed
// block. See PROTOCOL.md in category-labs/monad-domains.

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/cli/help_formatter.hpp>
#include <category/core/config.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/log.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/chain_id.hpp>
#include <category/execution/domain/deriver.hpp>
#include <category/execution/domain/domain_block.hpp>
#include <category/execution/domain/executor.hpp>
#include <category/execution/domain/hpke.hpp>
#include <category/execution/domain/input_queue.hpp>
#include <category/execution/domain/l1_source.hpp>
#include <category/execution/domain/statesync.hpp>
#include <category/execution/domain/statesync_listener.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/log_level_map.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/db/state_machine_init.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/chain/chain_factory.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/db/state_machine_init.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_error.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <CLI/CLI.hpp>
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
#include <utility>
#include <vector>

#include <unistd.h>

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

std::string validate_address(std::string const &value)
{
    std::string_view hex{value};
    skip_optional_hex_prefix(hex);
    auto const address = from_hex<Address>(value);
    if (hex.size() != sizeof(Address) * 2 || !address.has_value()) {
        return "address must contain exactly 20 bytes of hexadecimal";
    }
    if (*address == Address{}) {
        return "address must be nonzero";
    }
    return {};
}

std::string hex(byte_string_view const bytes)
{
    return "0x" + to_hex(bytes);
}

MONAD_ANONYMOUS_NAMESPACE_END

using namespace monad;
namespace fs = std::filesystem;

int main(int const argc, char const *argv[])
try {
    CLI::App cli{
        "Derive one private domain's blocks from the finalized chain of an L1 "
        "node, reading its triedb read-only, and execute them into a triedb of "
        "the domain's own. Without that triedb, the domain is derived from "
        "what the DomainHub's state holds of it: from its registration if no "
        "checkpoint is attested, otherwise from its state at the checkpoint, "
        "which --statesync-peer provides and the attested block hash "
        "verifies.",
        "monad-domain"};
    monad::cli::HelpFormatter{GIT_COMMIT_HASH}.install(cli);

    monad_chain_config chain_config{};
    fs::path l1_db_path;
    std::tuple<uint64_t, fs::path> domain;
    std::string hub_hex;
    fs::path domain_db_path;
    std::string statesync_peer;
    std::string statesync_listen;
    std::vector<std::string> statesync_allow;
    auto log_level = quill::LogLevel::Info;

    std::unordered_map<std::string, monad_chain_config> const CHAIN_CONFIG_MAP =
        {{"monad_devnet", CHAIN_CONFIG_MONAD_DEVNET},
         {"monad_testnet", CHAIN_CONFIG_MONAD_TESTNET},
         {"monad_mainnet", CHAIN_CONFIG_MONAD_MAINNET}};

    cli.add_option("--chain", chain_config, "the L1 chain config")
        ->required()
        ->transform(
            CLI::CheckedTransformer(CHAIN_CONFIG_MAP, CLI::ignore_case));
    cli.add_option("--l1-db", l1_db_path, "the L1 node's triedb")->required();
    auto key_file_validator = CLI::ExistingFile;
    key_file_validator.description("").application_index(1);
    cli.add_option(
           "--domain", domain, "the domain to derive and its HPKE receiver key")
        ->type_name("<CHAIN_ID> <PRIVATE_KEY_PEM_PATH>")
        ->required()
        ->check(key_file_validator);
    cli.add_option("--hub", hub_hex, "the L1 DomainHub address")
        ->type_name("ADDRESS")
        ->required()
        ->check(
            [](std::string const &value) { return validate_address(value); });
    cli.add_option(
           "--domain-db",
           domain_db_path,
           "the domain's own triedb, created when the domain's genesis is "
           "derived")
        ->required();
    cli.add_option(
           "--statesync-peer",
           statesync_peer,
           "a monad-domain of the same domain to get the domain's state from "
           "if there is no domain triedb and the hub has an attested "
           "checkpoint; the state goes over plain TCP")
        ->type_name("IP:PORT");
    auto *const statesync_listen_option =
        cli.add_option(
               "--statesync-listen",
               statesync_listen,
               "serve the domain's state at this address to the peers "
               "--statesync-allow names")
            ->type_name("IP:PORT");
    cli.add_option(
           "--statesync-allow",
           statesync_allow,
           "an address that may get the domain's state; may be repeated")
        ->type_name("IP")
        ->needs(statesync_listen_option);
    cli.add_option("--log-level", log_level, "level of logging")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::ParseError const &e) {
        return cli.exit(e);
    }

    init_root_logger(log_level);

    auto const &[domain_chain_id, key_path] = domain;
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
    Address const hub = *from_hex<Address>(hub_hex);

    // The domain db is created when the domain's genesis is derived.
    std::optional<fiber::PriorityPool> priority_pool;
    std::optional<vm::VM> vm;
    std::optional<mpt::Db> domain_db;
    std::optional<domain::PrivateDomainExecutor> executor;
    // Opened like the L1 node's db, but without an SQPOLL kernel thread, which
    // would spin on a CPU next to the L1 node's.
    auto const domain_db_config = [&](bool const append) {
        return mpt::OnDiskDbConfig{
            .append = append,
            .compaction = true,
            .rewind_to_latest_finalized = true,
            .sq_thread_cpu = std::nullopt,
            .dbname_path = domain_db_path};
    };
    // Opens the domain db, or creates it if `timestamp`, the domain's genesis
    // timestamp, is given.
    auto const open_executor = [&](std::optional<uint64_t> const timestamp) {
        if (timestamp.has_value()) {
            // Every L1 network is page-encoded, so is every domain block.
            MONAD_ASSERT(mip_8_active(chain->get_monad_revision(*timestamp)));
            domain_db.emplace(
                std::make_unique<MonadOnDiskMachine>(),
                domain_db_config(false));
        }
        else {
            register_ethereum_state_machines();
            register_monad_state_machines();
            domain_db.emplace(domain_db_config(true));
        }
        priority_pool.emplace(EXECUTION_THREADS, EXECUTION_FIBERS);
        vm.emplace();
        executor.emplace(
            *chain, domain_chain_id, hub, *domain_db, *vm, *priority_pool);
        LOG_INFO(
            "executing private domain {} into {}, from domain block {}",
            domain_chain_id,
            domain_db_path,
            executor->next_block());
    };
    if (fs::exists(domain_db_path)) {
        open_executor(std::nullopt);
    }

    mpt::AsyncIOContext io_ctx{
        mpt::ReadOnlyOnDiskDbConfig{.dbname_path = l1_db_path}};
    mpt::Db l1_db{io_ctx};
    domain::TrieDbL1Source const l1{l1_db};

    std::optional<domain::StatesyncListener> statesync_listener;
    if (!statesync_listen.empty()) {
        statesync_listener.emplace(
            statesync_listen, statesync_allow, domain_chain_id, domain_db_path);
        LOG_INFO(
            "serving private domain {}'s state on port {}",
            domain_chain_id,
            statesync_listener->port());
    }

    // Derivation continues with the block after the domain db's last: from
    // the logs of the L1 blocks while the L1 db has them, otherwise from the
    // blocks the hub's state holds, and from a peer's state at the hub's
    // checkpoint only if those start after the domain's next block.
    using Source = domain::DerivationStart::Source;
    auto planned = domain::plan_derivation_start(
        l1,
        hub,
        domain_chain_id,
        executor.has_value() ? executor->next_block() : 0);
    if (planned.has_error()) {
        LOG_ERROR(
            "cannot find where to continue private domain {}: {}",
            domain_chain_id,
            planned.assume_error().message().c_str());
        return EXIT_FAILURE;
    }
    auto const start = std::move(planned).value();
    if (start.source == Source::Checkpoint) {
        // The blocks up to the checkpoint are neither in the L1 db's history
        // nor in the hub's state: the domain's state at the checkpoint comes
        // from a peer, and is checked against the block hash the hub
        // attested.
        uint64_t const checkpoint_block = start.pending->next_block - 1;
        auto const &checkpoint_hash = start.pending->attested_block_hash;
        if (statesync_peer.empty()) {
            LOG_ERROR(
                "private domain {}'s blocks up to {} have left the L1 db's "
                "history, which starts at {}, and DomainHub {}'s input queue: "
                "pass --statesync-peer to get the domain's state at block {} "
                "from another monad-domain",
                domain_chain_id,
                checkpoint_block,
                l1_db.get_earliest_version(),
                hub_hex,
                checkpoint_block);
            return EXIT_FAILURE;
        }
        LOG_INFO(
            "syncing private domain {}'s state at block {}, hash {}, from {}",
            domain_chain_id,
            checkpoint_block,
            hex(to_byte_string_view(checkpoint_hash.bytes)),
            statesync_peer);
        // The state is loaded beside the domain db, and becomes it once it is
        // verified: until then a domain db that is behind stays as it is.
        fs::path syncing_path{domain_db_path};
        syncing_path += ".statesync";
        fs::remove(syncing_path);
        auto const peer = domain::connect_statesync_peer(statesync_peer);
        if (peer.has_error()) {
            LOG_ERROR("cannot connect to statesync peer {}", statesync_peer);
            return EXIT_FAILURE;
        }
        auto syncing_config = domain_db_config(false);
        syncing_config.dbname_path = syncing_path;
        auto const synced = domain::sync_domain_state(
            peer.value(),
            domain_chain_id,
            checkpoint_block,
            checkpoint_hash,
            syncing_config);
        ::close(peer.value());
        if (synced.has_error()) {
            fs::remove(syncing_path);
            LOG_ERROR(
                "syncing private domain {}'s state at block {} from {} "
                "failed: {}",
                domain_chain_id,
                checkpoint_block,
                statesync_peer,
                synced.assume_error().message().c_str());
            return EXIT_FAILURE;
        }
        if (executor.has_value()) {
            LOG_INFO(
                "replacing private domain {}'s db, whose next block is {}, "
                "with the synced state",
                domain_chain_id,
                executor->next_block());
            executor.reset();
            domain_db.reset();
        }
        fs::rename(syncing_path, domain_db_path);
        LOG_INFO(
            "synced private domain {}'s state at block {}",
            domain_chain_id,
            checkpoint_block);
        open_executor(std::nullopt);
        MONAD_ASSERT(executor->next_block() == start.cursor.next_block);
    }
    domain::PrivateDomainDeriver deriver{
        l1, key.value(), domain_chain_id, hub, start.cursor};

    auto const on_block =
        [&](domain::DerivedDomainBlock const &block) -> Result<void> {
        LOG_INFO(
            "domain block {} from L1 block {}, {} transactions",
            block.number,
            block.l1_block_number,
            block.transactions.size());
        std::string hashes;
        for (auto const &tx : block.transactions) {
            hashes += ' ';
            hashes += hex(to_byte_string_view(
                keccak256(rlp::encode_transaction(tx)).bytes));
        }
        LOG_DEBUG("domain block {} transactions:{}", block.number, hashes);
        if (!executor.has_value()) {
            MONAD_ASSERT(block.number == 0);
            open_executor(block.timestamp);
        }
        auto executed = executor->execute(block);
        if (executed.has_error()) {
            LOG_ERROR(
                "executing domain block {} failed: {}",
                block.number,
                executed.assume_error().message().c_str());
            return std::move(executed).as_failure();
        }
        LOG_INFO(
            "executed domain block {}, hash {}",
            block.number,
            hex(to_byte_string_view(executor->latest_block_hash().bytes)));
        return outcome::success();
    };

    if (start.pending.has_value()) {
        LOG_INFO(
            "deriving private domain {} from block {}, from the {} block(s) "
            "from block {} in DomainHub {}'s state as of L1 block {}",
            domain_chain_id,
            start.cursor.next_block,
            start.pending->blocks.size(),
            start.pending->next_block,
            hub_hex,
            start.pending_l1_block);
        auto const derived = deriver.derive_pending(
            *start.pending, start.pending_l1_block, on_block);
        if (derived.has_error()) {
            LOG_ERROR(
                "deriving private domain {} from the hub's state failed: {}",
                domain_chain_id,
                derived.assume_error().message().c_str());
            return EXIT_FAILURE;
        }
    }
    LOG_INFO(
        "deriving private domain {} from DomainHub {}'s logs, from L1 block "
        "{}",
        domain_chain_id,
        hub_hex,
        deriver.cursor().next_l1_block);

    signal(SIGINT, signal_handler);
    signal(SIGTERM, signal_handler);
    while (!stop) {
        auto const derived = deriver.derive_next(on_block);
        if (derived.has_error()) {
            if (derived.assume_error() ==
                mpt::DbError::version_no_longer_exist) {
                LOG_ERROR(
                    "L1 block {} has left the L1 db's history, which starts "
                    "at {}: derivation can no longer catch up from it",
                    deriver.cursor().next_l1_block,
                    l1_db.get_earliest_version());
            }
            else {
                LOG_ERROR(
                    "deriving L1 block {} failed: {}",
                    deriver.cursor().next_l1_block,
                    derived.assume_error().message().c_str());
            }
            return EXIT_FAILURE;
        }
        if (!derived.value()) {
            std::this_thread::sleep_for(POLL_INTERVAL);
        }
    }
    LOG_INFO("stopped at L1 block {}", deriver.cursor().next_l1_block);
    return EXIT_SUCCESS;
}
catch (std::exception const &e) {
    std::cerr << e.what() << '\n';
    return EXIT_FAILURE;
}
