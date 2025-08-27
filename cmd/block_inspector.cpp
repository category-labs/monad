// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/execution/ethereum/core/fmt/block_fmt.hpp>
#include <category/execution/ethereum/core/fmt/receipt_fmt.hpp>
#include <category/execution/ethereum/core/fmt/transaction_fmt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/receipt_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/util.hpp>

#include <CLI/CLI.hpp>
#include <quill/Quill.h>
#include <quill/bundled/fmt/core.h>
#include <quill/bundled/fmt/format.h>

#include <cstdint>
#include <filesystem>
#include <optional>
#include <vector>

using namespace monad;
using namespace monad::mpt;

int main(int argc, char *argv[])
{
    std::vector<std::filesystem::path> dbname_paths;
    auto log_level = quill::LogLevel::Info;
    std::optional<unsigned> tx_id = std::nullopt;
    std::optional<unsigned> receipt_id = std::nullopt;
    std::optional<unsigned> call_frame_id = std::nullopt;
    uint64_t block_number = INVALID_BLOCK_NUM;

    CLI::App cli{"monad-block-inspector"};
    cli.add_option(
           "--db",
           dbname_paths,
           "A comma-separated list of previously created database paths")
        ->required();
    cli.add_option("--block", block_number, "Block number to inspect")
        ->required();

    cli.add_option("--tx-id", tx_id, "Transaction ID to inspect");
    cli.add_option("--receipt-id", receipt_id, "Receipt ID to inspect");
    cli.add_option("--callframe-id", call_frame_id, "Call frame ID to inspect");

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        return cli.exit(e);
    }
    catch (CLI::RequiredError const &e) {
        return cli.exit(e);
    }
    auto stdout_handler = quill::stdout_handler();
    stdout_handler->set_pattern(
        "%(time) [%(thread_id)] %(file_name):%(line_number) LOG_%(log_level)\t"
        "%(message)",
        "%Y-%m-%d %H:%M:%S.%Qns",
        quill::Timezone::GmtTime);
    quill::Config cfg;
    cfg.default_handlers.emplace_back(stdout_handler);
    quill::configure(cfg);
    quill::start(true);
    quill::get_root_logger()->set_log_level(log_level);
    quill::flush();

    fmt::println("Opening read only database {}.", dbname_paths);
    ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = dbname_paths};
    AsyncIOContext io_ctx{ro_config};
    Db ro_db{io_ctx};
    fmt::println(
        "db summary: earliest_block_id={} latest_block_id={} "
        "latest_finalized_block_id={} last_verified_block_id={} "
        "history_length={}\n",
        ro_db.get_earliest_version(),
        ro_db.get_latest_version(),
        ro_db.get_latest_finalized_version(),
        ro_db.get_latest_verified_version(),
        ro_db.get_history_length());

    if (block_number >= ro_db.get_earliest_version() &&
        block_number <= ro_db.get_latest_version()) {
        fmt::println("Inspecting block {}\n", block_number);
        auto const block_header_res = ro_db.find(
            concat(finalized_nibbles, BLOCKHEADER_NIBBLE), block_number);
        if (!block_header_res) {
            LOG_ERROR(
                "Error: block header not found for block {} -- {}",
                block_number,
                block_header_res.error().message().c_str());
        }
        else {
            auto encoded_block_header = block_header_res.value().node->value();
            auto const block_header_res =
                rlp::decode_block_header(encoded_block_header);
            if (!block_header_res) {
                LOG_ERROR(
                    "Error: failed to decode block header for block {} -- {}",
                    block_number,
                    block_header_res.error().message().c_str());
            }
            else {
                auto const &block_header = block_header_res.value();
                fmt::println("Block Header: {}\n", block_header);
            }
        }
    }
    else {
        LOG_ERROR(
            "Error: block number {} is out of range [{}, {}]",
            block_number,
            ro_db.get_earliest_version(),
            ro_db.get_latest_version());
        return 1;
    }
    if (!tx_id && !receipt_id && !call_frame_id) {
        auto const transactions = get_transactions(ro_db, block_number);
        if (transactions.has_error()) {
            LOG_ERROR(
                "Error: failed to get transactions for block {} -- {}",
                block_number,
                transactions.error().message().c_str());
            return 1;
        }
        fmt::println(
            "Number of Transactions: {}\nTransactions: {}",
            transactions.value().size(),
            transactions.value());
        return 0;
    }
    if (tx_id) {
        auto const tx_res = ro_db.find(
            concat(
                finalized_nibbles,
                TRANSACTION_NIBBLE,
                mpt::NibblesView{rlp::encode_unsigned(tx_id.value())}),
            block_number);
        if (!tx_res) {
            LOG_ERROR(
                "Error: transaction id {} not found in block {} -- {}",
                tx_id.value(),
                block_number,
                tx_res.error().message().c_str());
        }
        else {
            auto encoded_tx = tx_res.value().node->value();
            auto const decode_res = decode_transaction_db(encoded_tx);
            if (!decode_res) {
                LOG_ERROR(
                    "Error: failed to decode transaction id {} in block {} -- "
                    "{}",
                    tx_id.value(),
                    block_number,
                    decode_res.error().message().c_str());
            }
            else {
                auto const &[tx, sender] = decode_res.value();
                fmt::println("Transaction ID {}: {}", tx_id.value(), tx);
                fmt::println("Sender: {}\n", sender);
            }
        }
    }

    if (receipt_id) {
        auto const receipt_res = ro_db.find(
            concat(
                finalized_nibbles,
                RECEIPT_NIBBLE,
                mpt::NibblesView{rlp::encode_unsigned(receipt_id.value())}),
            block_number);
        if (!receipt_res) {
            LOG_ERROR(
                "Error: receipt id {} not found in block {} -- {}",
                receipt_id.value(),
                block_number,
                receipt_res.error().message().c_str());
        }
        else {
            auto encoded_receipt = receipt_res.value().node->value();
            auto const decode_res = decode_receipt_db(encoded_receipt);
            if (!decode_res) {
                LOG_ERROR(
                    "Error: failed to decode receipt id {} in block {} -- {}",
                    receipt_id.value(),
                    block_number,
                    decode_res.error().message().c_str());
            }
            else {
                auto const &[receipt, log_index_begin] = decode_res.value();
                fmt::println("Receipt ID {}: {}", receipt_id.value(), receipt);
                fmt::println("Log index begin: {}", log_index_begin);
            }
        }
    }

    if (call_frame_id) {
        auto const callframe_res = ro_db.find(
            concat(
                finalized_nibbles,
                CALL_FRAME_NIBBLE,
                mpt::NibblesView{rlp::encode_unsigned(call_frame_id.value())}),
            block_number);
        if (!callframe_res) {
            LOG_ERROR(
                "Error: call frame id {} not found in block {} -- {}",
                call_frame_id.value(),
                block_number,
                callframe_res.error().message().c_str());
        }
        else {
            auto encoded_callframe = callframe_res.value().node->value();
            fmt::println(
                "Encoded call frame size: {}", encoded_callframe.size());
            fmt::println("Call frame format is not supported yet.");
        }
    }
}
