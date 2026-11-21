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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/derivation_error.hpp>
#include <category/execution/domain/deriver.hpp>
#include <category/execution/domain/input_queue.hpp>
#include <category/execution/domain/inputs.hpp>
#include <category/execution/domain/l1_source.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/mpt/db_error.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <map>
#include <optional>
#include <vector>

using namespace monad;
using namespace monad::domain;
using namespace monad::literals;

namespace
{
    constexpr uint64_t DOMAIN = 0x510000004eaf;
    constexpr Address HUB = 0x00000000000000000000000000000000000000aa_address;
    constexpr uint64_t L1_BLOCK = 500;
    constexpr uint64_t CAPACITY = uint64_t{1} << 17;

    // The hub's storage of one domain, written as InputQueue.sol and
    // DomainHub.sol write it. What is written is the storage as of L1_BLOCK,
    // the latest finalized L1 block; seal() keeps a copy as of an earlier one.
    class FakeHub final : public L1Source
    {
        using Storage = std::map<bytes32_t, bytes32_t>;

        Storage storage_;
        // The storage as of earlier L1 blocks, each until the next.
        std::map<uint64_t, Storage> sealed_;
        uint64_t head_{0};
        uint64_t tail_{0};

        static bytes32_t word(
            uint64_t const a, uint64_t const b, uint64_t const c,
            uint64_t const d)
        {
            bytes32_t result{};
            store_be(result.bytes, a);
            store_be(result.bytes + 8, b);
            store_be(result.bytes + 16, c);
            store_be(result.bytes + 24, d);
            return result;
        }

        void store_state()
        {
            storage_[input_queue_slot(DOMAIN, 1)] = word(0, 0, tail_, head_);
        }

    public:
        // The first L1 block the source still has.
        uint64_t history_start{0};

        // What is written so far is the storage from `l1_block_number` on.
        void seal(uint64_t const l1_block_number)
        {
            sealed_[l1_block_number] = storage_;
        }

        void store(uint64_t const index, bytes32_t const &value)
        {
            storage_[input_queue_slot(DOMAIN, index)] = value;
        }

        void push(bytes32_t const &value)
        {
            store(128 + head_ % CAPACITY, value);
            ++head_;
            store_state();
        }

        // Starts the ring at `position`, as if that many words had been
        // written and released.
        void start_at(uint64_t const position)
        {
            head_ = position;
            tail_ = position;
            store_state();
        }

        // Opens domain block `number`, derived from L1 block `l1_block_number`.
        void open_block(
            uint64_t const number, uint64_t const l1_block_number,
            uint64_t const slot_number = 0)
        {
            bytes32_t header{};
            header.bytes[0] = 4;
            store_be(header.bytes + 1, l1_block_number);
            store_be(header.bytes + 9, 1'000 + l1_block_number);
            store_be(header.bytes + 17, number);
            // The slot number has 56 bits.
            bytes32_t slot{};
            store_be(slot.bytes + 24, slot_number);
            std::copy(slot.bytes + 25, slot.bytes + 32, header.bytes + 25);
            push(header);
            bytes32_t prev_randao{};
            prev_randao.bytes[0] = 0x77;
            store_be(prev_randao.bytes + 24, number);
            push(prev_randao);
            store(0, word(1, 0, l1_block_number, number));
        }

        void push_input(
            uint8_t const kind, uint64_t const fee, byte_string_view payload)
        {
            bytes32_t header{};
            header.bytes[0] = kind;
            header.bytes[1] = static_cast<uint8_t>(payload.size() >> 24);
            header.bytes[2] = static_cast<uint8_t>(payload.size() >> 16);
            header.bytes[3] = static_cast<uint8_t>(payload.size() >> 8);
            header.bytes[4] = static_cast<uint8_t>(payload.size());
            store_be(header.bytes + 24, fee);
            push(header);
            while (!payload.empty()) {
                bytes32_t chunk{};
                chunk.bytes[0] = 1;
                auto const size = std::min<size_t>(31, payload.size());
                std::copy_n(payload.data(), size, chunk.bytes + 1);
                push(chunk);
                payload.remove_prefix(size);
            }
        }

        // A quorum attests `block_hash` and the hub releases every entry
        // written so far.
        void attest(bytes32_t const &block_hash)
        {
            storage_[attested_block_hash_slot(DOMAIN)] = block_hash;
            tail_ = head_;
            store_state();
        }

        uint64_t latest_finalized() const override
        {
            return L1_BLOCK;
        }

        Result<BlockHeader> read_finalized_header(uint64_t) const override
        {
            return mpt::DbError::version_no_longer_exist;
        }

        Result<std::vector<Receipt>>
        read_finalized_receipts(uint64_t) const override
        {
            return mpt::DbError::version_no_longer_exist;
        }

        uint64_t earliest() const override
        {
            return history_start;
        }

        Result<bytes32_t> read_storage(
            uint64_t const number, Address const &address,
            bytes32_t const &slot) const override
        {
            if (number < history_start || number > L1_BLOCK) {
                return mpt::DbError::version_no_longer_exist;
            }
            Storage const *storage = &storage_;
            if (number != L1_BLOCK) {
                auto const later = sealed_.upper_bound(number);
                if (later == sealed_.begin()) {
                    return bytes32_t{};
                }
                storage = &std::prev(later)->second;
            }
            auto const it = storage->find(slot);
            if (address != HUB || it == storage->end()) {
                return bytes32_t{};
            }
            return it->second;
        }
    };

    byte_string bytes(size_t const size, uint8_t const first)
    {
        byte_string result(size, 0);
        for (size_t i = 0; i < size; ++i) {
            result[i] = static_cast<uint8_t>(first + i);
        }
        return result;
    }

    // `sourceChainId(8) | from(20) | to(20) | nonce(8) | data`
    byte_string message_payload(
        uint64_t const source_chain_id, Address const &from, Address const &to,
        uint64_t const nonce, byte_string_view const data)
    {
        byte_string result(8, 0);
        store_be(result.data(), source_chain_id);
        result.append(from.bytes, sizeof(from.bytes));
        result.append(to.bytes, sizeof(to.bytes));
        result.append(8, 0);
        store_be(result.data() + 48, nonce);
        result.append(data);
        return result;
    }

    PendingDomainInputs read(FakeHub const &hub)
    {
        auto const pending =
            read_pending_domain_inputs(hub, HUB, DOMAIN, L1_BLOCK);
        EXPECT_TRUE(pending.has_value());
        EXPECT_TRUE(pending.value().has_value());
        return *pending.value();
    }

    void expect_malformed(FakeHub const &hub)
    {
        auto const pending =
            read_pending_domain_inputs(hub, HUB, DOMAIN, L1_BLOCK);
        ASSERT_TRUE(pending.has_error());
        EXPECT_EQ(pending.error(), DomainDerivationError::MalformedInputQueue);
    }
}

TEST(InputQueue, slots_follow_the_hub_layout)
{
    // cast keccak $(cast abi-encode "f(uint64,string)" 0x510000004eaf
    // "monad.domains.input-queue"), low 7 bits cleared.
    EXPECT_EQ(
        input_queue_slot(DOMAIN, 0),
        0xe5c326caf8a97b93042ade5f2dab865145ca7b8bdca70ab8e41ac0f6e3e48a80_bytes32);
    EXPECT_EQ(input_queue_slot(DOMAIN, 0), latest_domain_block_slot(DOMAIN));
    // The sum carries across bytes.
    EXPECT_EQ(
        input_queue_slot(DOMAIN, 128),
        0xe5c326caf8a97b93042ade5f2dab865145ca7b8bdca70ab8e41ac0f6e3e48b00_bytes32);
    EXPECT_EQ(
        input_queue_slot(DOMAIN, 128 + CAPACITY - 1),
        0xe5c326caf8a97b93042ade5f2dab865145ca7b8bdca70ab8e41ac0f6e3e68aff_bytes32);
    // cast index uint64 0x510000004eaf 3
    EXPECT_EQ(
        attested_block_hash_slot(DOMAIN),
        0x40fa4afadafa307517c55195c2ea4fd616abf33d4470454cc82546ba362642d8_bytes32);
}

TEST(InputQueue, an_unregistered_domain_has_nothing)
{
    FakeHub const hub;
    auto const pending = read_pending_domain_inputs(hub, HUB, DOMAIN, L1_BLOCK);
    ASSERT_TRUE(pending.has_value());
    EXPECT_FALSE(pending.value().has_value());
}

TEST(InputQueue, fails_like_the_l1_source)
{
    FakeHub const hub;
    auto const pending =
        read_pending_domain_inputs(hub, HUB, DOMAIN, L1_BLOCK + 1);
    ASSERT_TRUE(pending.has_error());
    EXPECT_EQ(pending.error(), mpt::DbError::version_no_longer_exist);
}

TEST(InputQueue, holds_the_domain_from_its_registration)
{
    FakeHub hub;
    hub.open_block(0, 100);

    auto const pending = read(hub);
    EXPECT_EQ(pending.attested_block_hash, bytes32_t{});
    EXPECT_EQ(pending.next_block, 0);
    ASSERT_EQ(pending.blocks.size(), 1);
    auto const &genesis = pending.blocks[0];
    EXPECT_TRUE(genesis.registered);
    EXPECT_EQ(genesis.l1_block_number, 100);
    EXPECT_EQ(genesis.timestamp, 1'100);
    EXPECT_EQ(genesis.prev_randao.bytes[0], 0x77);
    EXPECT_EQ(genesis.slot_number, 0);
    EXPECT_TRUE(genesis.inputs.empty());
}

TEST(InputQueue, decodes_every_input_kind)
{
    FakeHub hub;
    hub.open_block(0, 100);
    hub.open_block(1, 104, 0x00ab'cdef'0123'4567);
    // Payloads of no chunk, a full chunk, and a chunk and a byte.
    hub.push_input(1, 7, bytes(0, 0));
    hub.push_input(1, 8, bytes(31, 1));
    hub.push_input(1, 9, bytes(32, 2));
    hub.push_input(
        2,
        10,
        message_payload(
            20143, Address{0x1111}, Address{0x2222}, 5, bytes(70, 3)));
    hub.push_input(2, 11, message_payload(1, Address{}, Address{}, 6, {}));
    hub.push_input(3, 12, bytes(100, 4));
    hub.open_block(2, 109);
    hub.push_input(1, 13, bytes(62, 5));

    auto const pending = read(hub);
    EXPECT_EQ(pending.next_block, 0);
    ASSERT_EQ(pending.blocks.size(), 3);

    auto const &first = pending.blocks[1];
    EXPECT_FALSE(first.registered);
    EXPECT_EQ(first.l1_block_number, 104);
    EXPECT_EQ(first.slot_number, 0x00ab'cdef'0123'4567);
    EXPECT_EQ(
        first.inputs,
        (std::vector<DomainInput>{
            SequencedDomainPayload{.payload = bytes(0, 0), .fee = 7},
            SequencedDomainPayload{.payload = bytes(31, 1), .fee = 8},
            SequencedDomainPayload{.payload = bytes(32, 2), .fee = 9},
            L1DomainMessage{
                .source_chain_id = 20143,
                .from = Address{0x1111},
                .to = Address{0x2222},
                .data = bytes(70, 3),
                .nonce = 5,
                .fee = 10},
            L1DomainMessage{
                .source_chain_id = 1,
                .from = Address{},
                .to = Address{},
                .data = {},
                .nonce = 6,
                .fee = 11},
            EncryptedL1DomainMessage{}}));

    auto const &second = pending.blocks[2];
    EXPECT_EQ(second.l1_block_number, 109);
    EXPECT_EQ(
        second.inputs,
        (std::vector<DomainInput>{
            SequencedDomainPayload{.payload = bytes(62, 5), .fee = 13}}));
}

TEST(InputQueue, starts_after_the_attested_checkpoint)
{
    FakeHub hub;
    hub.open_block(0, 100);
    hub.open_block(1, 104);
    hub.push_input(1, 7, bytes(40, 1));
    hub.attest(bytes32_t{0xabcd});
    hub.open_block(2, 120);
    hub.push_input(1, 8, bytes(5, 2));
    hub.open_block(3, 121);

    auto const pending = read(hub);
    EXPECT_EQ(pending.attested_block_hash, bytes32_t{0xabcd});
    EXPECT_EQ(pending.next_block, 2);
    ASSERT_EQ(pending.blocks.size(), 2);
    EXPECT_FALSE(pending.blocks[0].registered);
    EXPECT_EQ(pending.blocks[0].l1_block_number, 120);
    EXPECT_EQ(pending.blocks[0].inputs.size(), 1);
    EXPECT_EQ(pending.blocks[1].l1_block_number, 121);
}

TEST(InputQueue, is_empty_when_the_checkpoint_covers_the_latest_block)
{
    FakeHub hub;
    hub.open_block(0, 100);
    hub.open_block(1, 104);
    hub.attest(bytes32_t{0xabcd});

    auto const pending = read(hub);
    EXPECT_EQ(pending.attested_block_hash, bytes32_t{0xabcd});
    EXPECT_EQ(pending.next_block, 2);
    EXPECT_TRUE(pending.blocks.empty());
}

TEST(InputQueue, wraps_around_the_ring)
{
    FakeHub hub;
    // The block entry's second word and the input's chunks wrap.
    hub.start_at(3 * CAPACITY - 1);
    hub.open_block(0, 100);
    hub.push_input(1, 7, bytes(90, 1));

    auto const pending = read(hub);
    ASSERT_EQ(pending.blocks.size(), 1);
    EXPECT_EQ(pending.blocks[0].prev_randao.bytes[0], 0x77);
    EXPECT_EQ(
        pending.blocks[0].inputs,
        (std::vector<DomainInput>{
            SequencedDomainPayload{.payload = bytes(90, 1), .fee = 7}}));
}

TEST(InputQueue, rejects_a_queue_the_hub_cannot_have_written)
{
    {
        // An input before any block entry.
        FakeHub hub;
        hub.open_block(0, 100);
        hub.attest(bytes32_t{1});
        hub.push_input(1, 7, bytes(5, 1));
        expect_malformed(hub);
    }
    {
        // A chunk without its tag.
        FakeHub hub;
        hub.open_block(0, 100);
        hub.push_input(1, 7, bytes(5, 1));
        hub.store(128 + 3, bytes32_t{});
        expect_malformed(hub);
    }
    {
        // A payload longer than what the queue holds.
        FakeHub hub;
        hub.open_block(0, 100);
        hub.push_input(1, 7, bytes(40, 1));
        bytes32_t header{};
        header.bytes[0] = 1;
        header.bytes[4] = 200;
        hub.store(128 + 2, header);
        expect_malformed(hub);
    }
    {
        // An unknown entry kind.
        FakeHub hub;
        hub.open_block(0, 100);
        hub.push_input(9, 7, bytes(5, 1));
        expect_malformed(hub);
    }
    {
        // A message shorter than its fixed fields.
        FakeHub hub;
        hub.open_block(0, 100);
        hub.push_input(2, 7, bytes(55, 1));
        expect_malformed(hub);
    }
    {
        // A block number that does not follow the one before it.
        FakeHub hub;
        hub.open_block(0, 100);
        hub.open_block(2, 104);
        expect_malformed(hub);
    }
    {
        // A block entry cut off by the head.
        FakeHub hub;
        hub.open_block(0, 100);
        hub.open_block(1, 104);
        hub.store(1, bytes32_t{3});
        expect_malformed(hub);
    }
    {
        // A latest block that is not the queue's last.
        FakeHub hub;
        hub.open_block(0, 100);
        hub.open_block(1, 104);
        bytes32_t latest{};
        latest.bytes[23] = 104;
        latest.bytes[31] = 5;
        hub.store(0, latest);
        expect_malformed(hub);
    }
}

namespace
{
    // A domain with a genesis from L1 block 100 and a block 1 from L1 block
    // 104.
    FakeHub two_blocks()
    {
        FakeHub hub;
        hub.open_block(0, 100);
        hub.seal(100);
        hub.open_block(1, 104);
        hub.push_input(1, 7, bytes(5, 1));
        hub.seal(104);
        return hub;
    }

    using Source = DerivationStart::Source;
}

TEST(AttestedBlock, none_until_a_checkpoint_is_attested)
{
    FakeHub hub;
    EXPECT_EQ(
        read_attested_domain_block(hub, HUB, DOMAIN, L1_BLOCK).value(),
        std::nullopt);

    hub.open_block(0, 5);
    hub.open_block(1, 6);
    EXPECT_EQ(
        read_attested_domain_block(hub, HUB, DOMAIN, L1_BLOCK).value(),
        std::nullopt);
}

TEST(AttestedBlock, is_the_block_before_the_first_the_queue_holds)
{
    FakeHub hub;
    hub.open_block(0, 5);
    hub.open_block(1, 6);
    hub.attest(bytes32_t{0xaa});
    hub.open_block(2, 8);
    hub.open_block(3, 9);

    EXPECT_EQ(
        read_attested_domain_block(hub, HUB, DOMAIN, L1_BLOCK).value(),
        (AttestedDomainBlock{.number = 1, .hash = bytes32_t{0xaa}}));
}

TEST(AttestedBlock, is_the_latest_block_when_the_queue_is_empty)
{
    FakeHub hub;
    hub.open_block(0, 5);
    hub.open_block(1, 6);
    hub.open_block(2, 8);
    hub.attest(bytes32_t{0xbb});

    EXPECT_EQ(
        read_attested_domain_block(hub, HUB, DOMAIN, L1_BLOCK).value(),
        (AttestedDomainBlock{.number = 2, .hash = bytes32_t{0xbb}}));
}

TEST(AttestedBlock, is_as_of_the_l1_block)
{
    FakeHub hub;
    hub.open_block(0, 5);
    hub.attest(bytes32_t{0xaa});
    hub.seal(6);
    hub.open_block(1, 8);
    hub.attest(bytes32_t{0xbb});

    EXPECT_EQ(
        read_attested_domain_block(hub, HUB, DOMAIN, 7).value(),
        (AttestedDomainBlock{.number = 0, .hash = bytes32_t{0xaa}}));
    EXPECT_EQ(
        read_attested_domain_block(hub, HUB, DOMAIN, L1_BLOCK).value(),
        (AttestedDomainBlock{.number = 1, .hash = bytes32_t{0xbb}}));
}

TEST(AttestedBlock, rejects_a_queue_the_hub_cannot_have_written)
{
    {
        // The first entry the checkpoint leaves opens no block.
        FakeHub hub;
        hub.open_block(0, 5);
        hub.attest(bytes32_t{0xaa});
        hub.push_input(1, 0, bytes(10, 1));
        auto const attested =
            read_attested_domain_block(hub, HUB, DOMAIN, L1_BLOCK);
        ASSERT_TRUE(attested.has_error());
        EXPECT_EQ(attested.error(), DomainDerivationError::MalformedInputQueue);
    }
    {
        // A checkpoint that does not cover the domain's genesis.
        FakeHub hub;
        hub.attest(bytes32_t{0xaa});
        hub.open_block(0, 5);
        auto const attested =
            read_attested_domain_block(hub, HUB, DOMAIN, L1_BLOCK);
        ASSERT_TRUE(attested.has_error());
        EXPECT_EQ(attested.error(), DomainDerivationError::MalformedInputQueue);
    }
}

TEST(AttestedBlock, fails_like_the_l1_source)
{
    FakeHub hub;
    hub.history_start = L1_BLOCK + 1;
    auto const attested =
        read_attested_domain_block(hub, HUB, DOMAIN, L1_BLOCK);
    ASSERT_TRUE(attested.has_error());
    EXPECT_EQ(attested.error(), mpt::DbError::version_no_longer_exist);
}

TEST(DerivationStart, logs_while_the_l1_has_them)
{
    auto const hub = two_blocks();
    for (uint64_t next_block = 0; next_block < 3; ++next_block) {
        auto const start = plan_derivation_start(hub, HUB, DOMAIN, next_block);
        ASSERT_TRUE(start.has_value());
        EXPECT_EQ(start.value().source, Source::Logs);
        EXPECT_FALSE(start.value().pending.has_value());
        // The L1 block of the next block, or the one after the latest if the
        // hub has no next block yet.
        EXPECT_EQ(
            start.value().cursor,
            (DerivationCursor{
                .next_l1_block =
                    std::array<uint64_t, 3>{100, 104, 501}[next_block],
                .next_block = next_block}));
    }

    // Before its registration a domain can only wait for it.
    FakeHub const unregistered;
    auto const start = plan_derivation_start(unregistered, HUB, DOMAIN, 0);
    ASSERT_TRUE(start.has_value());
    EXPECT_EQ(start.value().source, Source::Logs);
    EXPECT_EQ(
        start.value().cursor,
        (DerivationCursor{.next_l1_block = 501, .next_block = 0}));
}

TEST(DerivationStart, the_hubs_queue_once_the_logs_are_gone)
{
    auto hub = two_blocks();
    hub.history_start = 105;

    // With no domain state, and with the genesis only.
    for (uint64_t next_block = 0; next_block < 2; ++next_block) {
        auto const start = plan_derivation_start(hub, HUB, DOMAIN, next_block);
        ASSERT_TRUE(start.has_value());
        EXPECT_EQ(start.value().source, Source::Pending);
        EXPECT_EQ(start.value().pending_l1_block, L1_BLOCK);
        ASSERT_TRUE(start.value().pending.has_value());
        EXPECT_EQ(start.value().pending->next_block, 0);
        EXPECT_EQ(start.value().pending->blocks.size(), 2);
        EXPECT_EQ(
            start.value().cursor,
            (DerivationCursor{
                .next_l1_block = L1_BLOCK + 1, .next_block = next_block}));
    }

    // A domain that has every block needs neither.
    auto const start = plan_derivation_start(hub, HUB, DOMAIN, 2);
    ASSERT_TRUE(start.has_value());
    EXPECT_EQ(start.value().source, Source::Logs);
    EXPECT_EQ(
        start.value().cursor,
        (DerivationCursor{.next_l1_block = L1_BLOCK + 1, .next_block = 2}));
}

TEST(DerivationStart, the_checkpoint_once_the_queue_is_past_the_domain)
{
    auto hub = two_blocks();
    hub.attest(bytes32_t{0xabcd});
    hub.open_block(2, 120);
    hub.seal(120);
    hub.history_start = 121;

    // Blocks 0 and 1 are in neither the logs nor the queue.
    for (uint64_t next_block = 0; next_block < 2; ++next_block) {
        auto const start = plan_derivation_start(hub, HUB, DOMAIN, next_block);
        ASSERT_TRUE(start.has_value());
        EXPECT_EQ(start.value().source, Source::Checkpoint);
        ASSERT_TRUE(start.value().pending.has_value());
        EXPECT_EQ(
            start.value().pending->attested_block_hash, bytes32_t{0xabcd});
        EXPECT_EQ(start.value().pending->next_block, 2);
        EXPECT_EQ(
            start.value().cursor,
            (DerivationCursor{.next_l1_block = L1_BLOCK + 1, .next_block = 2}));
    }

    // A domain at the checkpoint has the queue.
    auto const start = plan_derivation_start(hub, HUB, DOMAIN, 2);
    ASSERT_TRUE(start.has_value());
    EXPECT_EQ(start.value().source, Source::Pending);
    EXPECT_EQ(
        start.value().cursor,
        (DerivationCursor{.next_l1_block = L1_BLOCK + 1, .next_block = 2}));
}

TEST(DerivationStart, fails_on_a_domain_the_hub_does_not_have)
{
    auto hub = two_blocks();
    auto ahead = plan_derivation_start(hub, HUB, DOMAIN, 5);
    ASSERT_TRUE(ahead.has_error());
    EXPECT_EQ(ahead.error(), DomainDerivationError::AheadOfHub);

    // The queue starts after the domain's next block, with no checkpoint to
    // have released the blocks before.
    hub.attest(bytes32_t{});
    hub.open_block(2, 120);
    hub.seal(120);
    hub.history_start = 121;
    auto const released = plan_derivation_start(hub, HUB, DOMAIN, 1);
    ASSERT_TRUE(released.has_error());
    EXPECT_EQ(released.error(), DomainDerivationError::MalformedInputQueue);
}
