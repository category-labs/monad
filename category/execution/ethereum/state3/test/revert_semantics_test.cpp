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

// Exercise rollback cases explicitly, including repeated field writes,
// nested acceptance followed by rejection, and reverted SELFDESTRUCT.
// A fixed pre-state isolates journal behavior from database behavior.
#include <category/core/byte_string.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/vm.hpp>

#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/vm/evm/traits.hpp>

#include <functional>

#include <cstdint>

using namespace monad;

namespace
{
    // Bit N reports failure of case N; the guest returns this mask.
    std::uint32_t failures = 0;
    unsigned current_case = 0;

    void check(bool const ok, char const *)
    {
        if (!ok) {
            failures |= (std::uint32_t{1} << current_case);
        }
    }

    Address addr(unsigned char const n)
    {
        Address a{};
        a.bytes[19] = n;
        return a;
    }

    bytes32_t key(unsigned char const n)
    {
        bytes32_t k{};
        k.bytes[31] = n;
        return k;
    }

    // A pre-state of two accounts and one slot. Everything else answers empty.
    struct StubDb final : Db
    {
        // Fixed arrays avoid std::map runtime helpers unavailable in the guest.
        struct AccountEntry
        {
            unsigned char id;
            Account account;
            bool set;
        };

        struct StorageEntry
        {
            unsigned char id, slot;
            bytes32_t value;
            bool set;
        };

        AccountEntry accounts[8]{};
        StorageEntry storage[8]{};

        void put_account(unsigned char const id, Account const &a)
        {
            for (auto &entry : accounts) {
                if (!entry.set) {
                    entry = {id, a, true};
                    return;
                }
            }
        }

        void put_storage(
            unsigned char const id, unsigned char const slot,
            bytes32_t const &v)
        {
            for (auto &entry : storage) {
                if (!entry.set) {
                    entry = {id, slot, v, true};
                    return;
                }
            }
        }

        bool is_page_encoded() const override
        {
            return false;
        }

        std::optional<Account> read_account(monad_address const &a) override
        {
            for (auto const &entry : accounts) {
                if (entry.set && entry.id == a.bytes[19]) {
                    return entry.account;
                }
            }
            return std::nullopt;
        }

        bytes32_t read_storage(
            monad_address const &a, Incarnation, bytes32_t const &k) override
        {
            for (auto const &entry : storage) {
                if (entry.set && entry.id == a.bytes[19] &&
                    entry.slot == k.bytes[31]) {
                    return entry.value;
                }
            }
            return bytes32_t{};
        }

        storage_page_t read_storage_page(
            Address const &, Incarnation, bytes32_t const &) override
        {
            return {};
        }

        vm::SharedIntercode read_code(bytes32_t const &) override
        {
            return {};
        }

        BlockHeader read_eth_header() override
        {
            return {};
        }

        bytes32_t state_root() override
        {
            return {};
        }

        bytes32_t receipts_root() override
        {
            return {};
        }

        bytes32_t transactions_root() override
        {
            return {};
        }

        std::optional<bytes32_t> withdrawals_root() override
        {
            return std::nullopt;
        }

        void set_block_and_prefix(uint64_t, bytes32_t const &) override {}

        void finalize(uint64_t, bytes32_t const &) override {}

        void update_verified_block(uint64_t) override {}

        void update_voted_metadata(uint64_t, bytes32_t const &) override {}

        void update_proposed_metadata(uint64_t, bytes32_t const &) override {}

        uint64_t get_block_number() const override
        {
            return 0;
        }

        void commit(
            bytes32_t const &, CommitBuilder &, BlockHeader const &,
            StateDeltas const &, std::function<void(BlockHeader &)>) override
        {
        }
    };
}

// Returns a bitmask: bit N set means case N failed, 0 means every case passed.
extern "C" std::uint32_t monad_zkvm_revert_semantics_test(void)
{
    failures = 0;

    current_case = 1;
    // ---- 1. parent writes, child ACCEPTS, parent REJECTS.
    // Accepting the child retains its undo records so rejecting the parent
    // restores the values from before both frames.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 7});
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        // Load before push so rejection restores fields rather than erasing the
        // row.
        state.set_nonce(addr(1), state.get_nonce(addr(1)));
        state.push();
        state.set_nonce(addr(1), 8); // parent
        state.push();
        state.set_nonce(addr(1), 9); // child
        state.pop_accept();
        check(
            state.get_nonce(addr(1)) == 9,
            "1: accepted child's write survives the accept");
        state.pop_reject();
        check(
            state.get_nonce(addr(1)) == 7,
            "1: parent reject undoes BOTH writes");
    }

    current_case = 2;
    // ---- 2. parent writes, child REJECTS, parent ACCEPTS.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 7});
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        state.push();
        state.set_nonce(addr(1), 8);
        state.push();
        state.set_nonce(addr(1), 9);
        state.pop_reject();
        check(
            state.get_nonce(addr(1)) == 8,
            "2: child reject restores the PARENT's value, not the db's");
        state.pop_accept();
        check(state.get_nonce(addr(1)) == 8, "2: parent accept keeps it");
    }

    current_case = 3;
    // ---- 3. the same field written twice in one frame, then rejected.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 7});
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        // Load before push so rejection restores fields rather than erasing the
        // row.
        state.set_nonce(addr(1), state.get_nonce(addr(1)));
        state.push();
        state.set_nonce(addr(1), 8);
        state.set_nonce(addr(1), 9);
        state.set_nonce(addr(1), 10);
        state.pop_reject();
        check(
            state.get_nonce(addr(1)) == 7,
            "3: three writes in one frame revert to the pre-frame value");
    }

    current_case = 4;
    // ---- 4. a row CREATED in the frame, then rejected: it must be gone, not
    // merely restored.
    {
        StubDb db; // account 2 does not exist
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        check(!state.account_exists(addr(2)), "4: absent before");
        state.push();
        state.add_to_balance(addr(2), 100);
        check(state.account_exists(addr(2)), "4: present after the write");
        state.pop_reject();
        check(
            !state.account_exists(addr(2)),
            "4: reject erases a row the frame created");
        // An absent account is not enough: a leftover row would still be
        // committed. Require the Created record to erase the row itself.
        check(
            state.current().find(addr(2)) == state.current().end(),
            "4: and the ROW itself is gone from current_, not merely emptied");
    }

    current_case = 5;
    // ---- 5. SELFDESTRUCT then revert. Zero occurrences in the corpus.
    {
        StubDb db;
        db.put_account(1, Account{.balance = 500, .nonce = 1});
        db.put_account(3, Account{.nonce = 0});
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        // Load before push so rejection restores fields rather than erasing the
        // row.
        state.set_nonce(addr(1), state.get_nonce(addr(1)));
        state.push();
        state.selfdestruct<EvmTraits<EvmRevision::Shanghai>>(addr(1), addr(3));
        check(state.is_destructed(addr(1)), "5: destructed inside the frame");
        state.pop_reject();
        check(
            !state.is_destructed(addr(1)),
            "5: reject clears the destruct flag");
        check(
            state.get_balance(addr(1)) == 500, "5: and gives the balance back");
    }

    current_case = 6;
    // ---- 6. storage and transient storage.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        db.put_storage(1, 5, key(42));
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        // Load before push so rejection restores fields rather than erasing the
        // row.
        state.set_nonce(addr(1), state.get_nonce(addr(1)));
        state.push();
        state.set_storage(addr(1), key(5), key(99));
        state.set_transient_storage(addr(1), key(6), key(77));
        check(
            state.get_storage(addr(1), key(5)) == key(99),
            "6: storage written");
        check(
            state.get_transient_storage(addr(1), key(6)) == key(77),
            "6: transient written");
        state.pop_reject();
        check(
            state.get_storage(addr(1), key(5)) == key(42),
            "6: storage reverts to the db value");
        check(
            state.get_transient_storage(addr(1), key(6)) == bytes32_t{},
            "6: transient reverts to empty");
    }

    current_case = 7;
    // ---- 7. EIP-2929: a key warmed in a frame that reverts must be cold
    // again.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        // Load before push so rejection restores fields rather than erasing the
        // row.
        state.set_nonce(addr(1), state.get_nonce(addr(1)));
        state.push();
        check(
            state.access_account(addr(1)) == AccessStatus::Cold,
            "7: account cold first");
        check(
            state.access_account(addr(1)) == AccessStatus::Warm,
            "7: then warm");
        check(
            state.access_storage<EvmTraits<EvmRevision::Shanghai>>(
                addr(1), key(5)) == AccessStatus::Cold,
            "7: slot cold first");
        check(
            state.access_storage<EvmTraits<EvmRevision::Shanghai>>(
                addr(1), key(5)) == AccessStatus::Warm,
            "7: then warm");
        state.pop_reject();
        state.push();
        check(
            state.access_account(addr(1)) == AccessStatus::Cold,
            "7: account COLD again after reject");
        check(
            state.access_storage<EvmTraits<EvmRevision::Shanghai>>(
                addr(1), key(5)) == AccessStatus::Cold,
            "7: slot COLD again after reject");
        state.pop_accept();
    }

    current_case = 8;
    // 8. Restore an existing overlay slot after a child rejection.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        db.put_storage(1, 5, key(42));
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        state.push();
        state.set_storage(addr(1), key(5), key(99)); // now in the overlay
        state.push();
        state.set_storage(addr(1), key(5), key(123));
        state.pop_reject();
        check(
            state.get_storage(addr(1), key(5)) == key(99),
            "8: reject restores the overlay value, not the db value");
        state.pop_accept();
        check(
            state.get_storage(addr(1), key(5)) == key(99),
            "8: and the accept keeps it");
    }

    current_case = 9;
    // 9. Repeated writes to one slot must restore its original value on
    // rollback.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        db.put_storage(1, 5, key(42));
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        // Load before push so rejection restores fields rather than erasing the
        // row.
        state.set_nonce(addr(1), state.get_nonce(addr(1)));
        state.push();
        state.set_storage(addr(1), key(5), key(1));
        state.set_storage(addr(1), key(5), key(2));
        state.set_storage(addr(1), key(5), key(3));
        check(
            state.get_storage(addr(1), key(5)) == key(3), "9: last write wins");
        state.pop_reject();
        check(
            state.get_storage(addr(1), key(5)) == key(42),
            "9: reject goes back to the db value, not to an intermediate one");
    }

    current_case = 10;
    // 10. A parent rejection must undo slot writes from an accepted child.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        db.put_storage(1, 5, key(42));
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        // Load before push so rejection restores fields rather than erasing the
        // row.
        state.set_nonce(addr(1), state.get_nonce(addr(1)));
        state.push();
        state.set_storage(addr(1), key(5), key(7)); // parent
        state.push();
        state.set_storage(addr(1), key(5), key(8)); // child
        state.set_storage(
            addr(1), key(6), key(9)); // a slot only the child touches
        state.pop_accept();
        check(
            state.get_storage(addr(1), key(5)) == key(8),
            "10: accepted child's write survives");
        check(
            state.get_storage(addr(1), key(6)) == key(9),
            "10: and its new slot too");
        state.pop_reject();
        check(
            state.get_storage(addr(1), key(5)) == key(42),
            "10: parent reject undoes BOTH writes to the shared slot");
        check(
            state.get_storage(addr(1), key(6)) == bytes32_t{},
            "10: and removes the slot only the child added");
    }

    current_case = 11;
    // 11. Nested rollback restores balances and reverses the touched
    // transition.
    {
        StubDb db;
        db.put_account(1, Account{.balance = 1000, .nonce = 1});
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        check(!state.is_touched(addr(1)), "11: not touched to begin with");
        // Load before push so rejection restores fields rather than erasing the
        // row.
        state.access_account(addr(1));
        state.push();
        state.add_to_balance(addr(1), 50);
        state.push();
        state.subtract_from_balance(addr(1), 300);
        state.add_to_balance(addr(1), 7);
        check(
            state.get_balance(addr(1)) == 757, "11: nested arithmetic applies");
        state.pop_reject();
        check(
            state.get_balance(addr(1)) == 1050,
            "11: child reject restores the parent's balance");
        state.pop_reject();
        check(
            state.get_balance(addr(1)) == 1000,
            "11: parent reject restores the db balance");
        check(!state.is_touched(addr(1)), "11: and `touched` is false again");
    }

    current_case = 12;
    // 12. Restore code_hash after rejection.
    {
        StubDb db;
        db.put_account(
            1, Account{.balance = 1, .code_hash = NULL_HASH, .nonce = 1});
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        // Load before push so rejection restores fields rather than erasing the
        // row.
        state.access_account(addr(1));
        state.push();
        unsigned char const code[] = {0x60, 0x00, 0x60, 0x00, 0xf3};
        state.set_code(addr(1), byte_string_view{code, sizeof(code)});
        check(
            state.get_code_hash(addr(1)) != NULL_HASH, "12: code hash changed");
        state.pop_reject();
        check(
            state.get_code_hash(addr(1)) == NULL_HASH,
            "12: reject restores the code hash");
    }

    current_case = 13;
    // 13. Rejecting account materialisation must restore absence, not an empty
    // account.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        check(!state.account_exists(addr(9)), "13: absent to begin with");
        // Load before push so rejection restores fields rather than erasing the
        // row. access_account leaves account_ absent, which is what this case
        // needs.
        state.access_account(addr(9));
        state.push();
        state.set_nonce(addr(9), 5);
        check(state.account_exists(addr(9)), "13: the mutator materialised it");
        check(state.get_nonce(addr(9)) == 5, "13: and wrote the field");
        state.pop_reject();
        check(
            !state.account_exists(addr(9)),
            "13: reject leaves NO account, not an empty one");
    }

    current_case = 14;
    // 14. Restore PageTracker directly; Ethereum traits never activate MIP-8.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{0, 0}};
        // Load before push so rejection restores fields rather than erasing the
        // row.
        state.access_account(addr(1));
        state.push();
        auto const first =
            state.update_page(addr(1), key(5), StorageStatus::Added);
        state.pop_reject();
        state.push();
        auto const again =
            state.update_page(addr(1), key(5), StorageStatus::Added);
        check(
            again.first_page_write == first.first_page_write &&
                again.grew_state == first.grew_state,
            "14: after a reject the page map is as it was, so the same update "
            "answers the same");
        state.pop_accept();
    }

    current_case = 15;
    // 15. Restore an existing account's incarnation, not just its fields.
    {
        StubDb db;
        db.put_account(
            1, Account{.balance = 5, .code_hash = NULL_HASH, .nonce = 0});
        vm::VM vm;
        BlockState block_state{db, vm};
        State state{block_state, Incarnation{1, 0}};
        check(
            !state.is_current_incarnation(addr(1)),
            "15: a foreign incarnation to begin with");
        // Load before push so rejection restores fields rather than erasing the
        // row.
        state.access_account(addr(1));
        state.push();
        state.set_to_state_incarnation(addr(1));
        check(
            state.is_current_incarnation(addr(1)),
            "15: moved to this state's incarnation");
        state.pop_reject();
        check(
            !state.is_current_incarnation(addr(1)),
            "15: reject puts the old incarnation back");
        check(
            state.get_balance(addr(1)) == 5,
            "15: and leaves the rest of the account alone");
    }

    return failures;
}
