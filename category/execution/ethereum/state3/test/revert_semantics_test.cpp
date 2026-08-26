// Revert semantics of State's undo log, on the paths a mainnet corpus cannot reach.
//
// WHY THIS EXISTS. The 200-block corpus gate does exercise the journal, and heavily: measured on
// 25815000-25815199 it rejects 10,011 frames at mean depth 5.86, replays 115,391 records, and
// 78 % of those had been PROMOTED by an accepted child -- the subtle case, covered by accident.
// Two cases it never reaches at all:
//
//   * SELFDESTRUCT then revert. Since EIP-6780 the account is only deleted when it was created in
//     the same transaction, so the case is near-extinct on modern mainnet. Measured: 0 occurrences
//     in 200 blocks. No larger corpus fixes that.
//   * A field written twice in one frame. Whole-row journalling absorbs it by construction today,
//     so the corpus cannot tell a correct implementation from one that journals every write and
//     replays them out of order. It becomes discriminating the moment records go per-field.
//
// A stub Db serves a fixed pre-state, so every assertion is about the journal and nothing else.
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
    // Bit N is set when case N failed. No printing: this runs in the guest, which has no
    // stdio, and a bitmask is what a caller on either target can read.
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
        // Flat, not std::map: the guest's libstdc++ stubs carry no red-black tree helpers,
        // because nothing in the guest uses std::map. Eight of each is more than any case needs.
        struct AccEntry { unsigned char id; Account acct; bool set; };
        struct StoEntry { unsigned char id, slot; bytes32_t val; bool set; };
        AccEntry accounts[8]{};
        StoEntry storage[8]{};

        void put_account(unsigned char const id, Account const &a)
        {
            for (auto &e : accounts) {
                if (!e.set) { e = {id, a, true}; return; }
            }
        }

        void put_storage(unsigned char const id, unsigned char const slot,
                         bytes32_t const &v)
        {
            for (auto &e : storage) {
                if (!e.set) { e = {id, slot, v, true}; return; }
            }
        }

        bool is_page_encoded() const override { return false; }

        std::optional<Account> read_account(Address const &a) override
        {
            for (auto const &e : accounts) {
                if (e.set && e.id == a.bytes[19]) {
                    return e.acct;
                }
            }
            return std::nullopt;
        }

        bytes32_t read_storage(
            Address const &a, Incarnation, bytes32_t const &k) override
        {
            for (auto const &e : storage) {
                if (e.set && e.id == a.bytes[19] && e.slot == k.bytes[31]) {
                    return e.val;
                }
            }
            return bytes32_t{};
        }

        storage_page_t read_storage_page(
            Address const &, Incarnation, bytes32_t const &) override
        {
            return {};
        }

        vm::SharedIntercode read_code(bytes32_t const &) override { return {}; }
        BlockHeader read_eth_header() override { return {}; }
        bytes32_t state_root() override { return {}; }
        bytes32_t receipts_root() override { return {}; }
        bytes32_t transactions_root() override { return {}; }
        std::optional<bytes32_t> withdrawals_root() override { return std::nullopt; }
        void set_block_and_prefix(uint64_t, bytes32_t const &) override {}
        void finalize(uint64_t, bytes32_t const &) override {}
        void update_verified_block(uint64_t) override {}
        void update_voted_metadata(uint64_t, bytes32_t const &) override {}
        void update_proposed_metadata(uint64_t, bytes32_t const &) override {}
        uint64_t get_block_number() const override { return 0; }

        void commit(
            bytes32_t const &, CommitBuilder &, BlockHeader const &,
            StateDeltas const &,
            std::function<void(BlockHeader &)>) override
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
    // The record the child left behind carries the pre-PARENT value, so the parent's own write
    // must disappear too. This is the case the corpus covers 89,826 times; asserted here because
    // the reasoning it rests on -- a row the child was first to touch was untouched by the parent
    // -- is the one thing that makes leaving records to the parent correct.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 7});
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        // The row must exist in current_ BEFORE the frame opens. A mutator that creates it inside
        // the frame gets a Created record, and Created erases the whole row on reject -- which
        // restores the value by accident and makes the narrow record below untestable.
        st.set_nonce(addr(1), st.get_nonce(addr(1)));
        st.push();
        st.set_nonce(addr(1), 8);           // parent
        st.push();
        st.set_nonce(addr(1), 9);           // child
        st.pop_accept();
        check(st.get_nonce(addr(1)) == 9, "1: accepted child's write survives the accept");
        st.pop_reject();
        check(st.get_nonce(addr(1)) == 7, "1: parent reject undoes BOTH writes");
    }

    current_case = 2;
    // ---- 2. parent writes, child REJECTS, parent ACCEPTS.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 7});
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        st.push();
        st.set_nonce(addr(1), 8);
        st.push();
        st.set_nonce(addr(1), 9);
        st.pop_reject();
        check(st.get_nonce(addr(1)) == 8, "2: child reject restores the PARENT's value, not the db's");
        st.pop_accept();
        check(st.get_nonce(addr(1)) == 8, "2: parent accept keeps it");
    }

    current_case = 3;
    // ---- 3. the same field written twice in one frame, then rejected.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 7});
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        // The row must exist in current_ BEFORE the frame opens. A mutator that creates it inside
        // the frame gets a Created record, and Created erases the whole row on reject -- which
        // restores the value by accident and makes the narrow record below untestable.
        st.set_nonce(addr(1), st.get_nonce(addr(1)));
        st.push();
        st.set_nonce(addr(1), 8);
        st.set_nonce(addr(1), 9);
        st.set_nonce(addr(1), 10);
        st.pop_reject();
        check(st.get_nonce(addr(1)) == 7, "3: three writes in one frame revert to the pre-frame value");
    }

    current_case = 4;
    // ---- 4. a row CREATED in the frame, then rejected: it must be gone, not merely restored.
    {
        StubDb db;                          // account 2 does not exist
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        check(!st.account_exists(addr(2)), "4: absent before");
        st.push();
        st.add_to_balance(addr(2), 100);
        check(st.account_exists(addr(2)), "4: present after the write");
        st.pop_reject();
        check(!st.account_exists(addr(2)), "4: reject erases a row the frame created");
        // account_exists() cannot tell "the row is gone" from "the row is still listed with an empty
        // account", and the typed records restore the second on their own -- so without this the
        // case passes with no Created record at all. The distinction is not academic: BlockState
        // commits every row current_ lists, so a row left behind enters the commit set.
        check(st.current().find(addr(2)) == st.current().end(),
              "4: and the ROW itself is gone from current_, not merely emptied");
    }

    current_case = 5;
    // ---- 5. SELFDESTRUCT then revert. Zero occurrences in the corpus.
    {
        StubDb db;
        db.put_account(1, Account{.balance = 500, .nonce = 1});
        db.put_account(3, Account{.nonce = 0});
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        // The row must exist in current_ BEFORE the frame opens. A mutator that creates it inside
        // the frame gets a Created record, and Created erases the whole row on reject -- which
        // restores the value by accident and makes the narrow record below untestable.
        st.set_nonce(addr(1), st.get_nonce(addr(1)));
        st.push();
        st.selfdestruct<EvmTraits<MONAD_ETH_SHANGHAI>>(addr(1), addr(3));
        check(st.is_destructed(addr(1)), "5: destructed inside the frame");
        st.pop_reject();
        check(!st.is_destructed(addr(1)), "5: reject clears the destruct flag");
        check(st.get_balance(addr(1)) == 500, "5: and gives the balance back");
    }

    current_case = 6;
    // ---- 6. storage and transient storage.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        db.put_storage(1, 5, key(42));
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        // The row must exist in current_ BEFORE the frame opens. A mutator that creates it inside
        // the frame gets a Created record, and Created erases the whole row on reject -- which
        // restores the value by accident and makes the narrow record below untestable.
        st.set_nonce(addr(1), st.get_nonce(addr(1)));
        st.push();
        st.set_storage(addr(1), key(5), key(99));
        st.set_transient_storage(addr(1), key(6), key(77));
        check(st.get_storage(addr(1), key(5)) == key(99), "6: storage written");
        check(st.get_transient_storage(addr(1), key(6)) == key(77), "6: transient written");
        st.pop_reject();
        check(st.get_storage(addr(1), key(5)) == key(42), "6: storage reverts to the db value");
        check(st.get_transient_storage(addr(1), key(6)) == bytes32_t{}, "6: transient reverts to empty");
    }

    current_case = 7;
    // ---- 7. EIP-2929: a key warmed in a frame that reverts must be cold again.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        // The row must exist in current_ BEFORE the frame opens. A mutator that creates it inside
        // the frame gets a Created record, and Created erases the whole row on reject -- which
        // restores the value by accident and makes the narrow record below untestable.
        st.set_nonce(addr(1), st.get_nonce(addr(1)));
        st.push();
        check(st.access_account(addr(1)) == EVMC_ACCESS_COLD, "7: account cold first");
        check(st.access_account(addr(1)) == EVMC_ACCESS_WARM, "7: then warm");
        check(st.access_storage<EvmTraits<MONAD_ETH_SHANGHAI>>(addr(1), key(5)) == EVMC_ACCESS_COLD,
              "7: slot cold first");
        check(st.access_storage<EvmTraits<MONAD_ETH_SHANGHAI>>(addr(1), key(5)) == EVMC_ACCESS_WARM,
              "7: then warm");
        st.pop_reject();
        st.push();
        check(st.access_account(addr(1)) == EVMC_ACCESS_COLD, "7: account COLD again after reject");
        check(st.access_storage<EvmTraits<MONAD_ETH_SHANGHAI>>(addr(1), key(5)) == EVMC_ACCESS_COLD,
              "7: slot COLD again after reject");
        st.pop_accept();
    }

    current_case = 8;
    // ---- 8. a slot ALREADY in the overlay, overwritten in a frame that reverts.
    // Case 6 covers the other branch: a slot absent from the overlay, whose record says "remove it
    // again". This one says "put the old value back", and the two are the whole of what a slot
    // record can mean.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        db.put_storage(1, 5, key(42));
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        st.push();
        st.set_storage(addr(1), key(5), key(99));   // now in the overlay
        st.push();
        st.set_storage(addr(1), key(5), key(123));
        st.pop_reject();
        check(st.get_storage(addr(1), key(5)) == key(99),
              "8: reject restores the overlay value, not the db value");
        st.pop_accept();
        check(st.get_storage(addr(1), key(5)) == key(99), "8: and the accept keeps it");
    }

    current_case = 9;
    // ---- 9. several writes to the SAME slot inside one frame.
    // A slot is journalled on every write, not on the frame's first, so this frame leaves three
    // records for one slot. Replayed backwards the oldest has to land last.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        db.put_storage(1, 5, key(42));
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        // The row must exist in current_ BEFORE the frame opens. A mutator that creates it inside
        // the frame gets a Created record, and Created erases the whole row on reject -- which
        // restores the value by accident and makes the narrow record below untestable.
        st.set_nonce(addr(1), st.get_nonce(addr(1)));
        st.push();
        st.set_storage(addr(1), key(5), key(1));
        st.set_storage(addr(1), key(5), key(2));
        st.set_storage(addr(1), key(5), key(3));
        check(st.get_storage(addr(1), key(5)) == key(3), "9: last write wins");
        st.pop_reject();
        check(st.get_storage(addr(1), key(5)) == key(42),
              "9: reject goes back to the db value, not to an intermediate one");
    }

    current_case = 10;
    // ---- 10. child writes a slot and is ACCEPTED, parent REJECTS.
    // The slot equivalent of case 1: the child's records stay in the log under the parent's mark,
    // so the parent's reject has to undo the accepted child's slot write too.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        db.put_storage(1, 5, key(42));
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        // The row must exist in current_ BEFORE the frame opens. A mutator that creates it inside
        // the frame gets a Created record, and Created erases the whole row on reject -- which
        // restores the value by accident and makes the narrow record below untestable.
        st.set_nonce(addr(1), st.get_nonce(addr(1)));
        st.push();
        st.set_storage(addr(1), key(5), key(7));    // parent
        st.push();
        st.set_storage(addr(1), key(5), key(8));    // child
        st.set_storage(addr(1), key(6), key(9));    // a slot only the child touches
        st.pop_accept();
        check(st.get_storage(addr(1), key(5)) == key(8), "10: accepted child's write survives");
        check(st.get_storage(addr(1), key(6)) == key(9), "10: and its new slot too");
        st.pop_reject();
        check(st.get_storage(addr(1), key(5)) == key(42),
              "10: parent reject undoes BOTH writes to the shared slot");
        check(st.get_storage(addr(1), key(6)) == bytes32_t{},
              "10: and removes the slot only the child added");
    }

    current_case = 11;
    // ---- 11. balance, nested, and the `touched` flag it sets.
    // Balance has its own narrow record now, and add_to_balance also flips `touched`; the flag is
    // journalled only on a real transition, so a frame that touches twice must still restore once.
    {
        StubDb db;
        db.put_account(1, Account{.balance = 1000, .nonce = 1});
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        check(!st.is_touched(addr(1)), "11: not touched to begin with");
        // The row must exist in current_ BEFORE the frame opens. A mutator that creates it inside
        // the frame gets a Created record, and Created erases the whole row on reject -- which
        // restores the value by accident and makes the narrow record below untestable.
        st.access_account(addr(1));
        st.push();
        st.add_to_balance(addr(1), 50);
        st.push();
        st.subtract_from_balance(addr(1), 300);
        st.add_to_balance(addr(1), 7);
        check(st.get_balance(addr(1)) == 757, "11: nested arithmetic applies");
        st.pop_reject();
        check(st.get_balance(addr(1)) == 1050, "11: child reject restores the parent's balance");
        st.pop_reject();
        check(st.get_balance(addr(1)) == 1000, "11: parent reject restores the db balance");
        check(!st.is_touched(addr(1)), "11: and `touched` is false again");
    }

    current_case = 12;
    // ---- 12. code_hash: set_code in a frame that reverts.
    {
        StubDb db;
        db.put_account(1, Account{.balance = 1, .code_hash = NULL_HASH, .nonce = 1});
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        // The row must exist in current_ BEFORE the frame opens. A mutator that creates it inside
        // the frame gets a Created record, and Created erases the whole row on reject -- which
        // restores the value by accident and makes the narrow record below untestable.
        st.access_account(addr(1));
        st.push();
        unsigned char const code[] = {0x60, 0x00, 0x60, 0x00, 0xf3};
        st.set_code(addr(1), byte_string_view{code, sizeof(code)});
        check(st.get_code_hash(addr(1)) != NULL_HASH, "12: code hash changed");
        st.pop_reject();
        check(st.get_code_hash(addr(1)) == NULL_HASH, "12: reject restores the code hash");
    }

    current_case = 13;
    // ---- 13. a mutation on an account that does NOT exist, then rejected.
    // The mutators materialise an Account before writing, so the record has to say "there was no
    // account" -- not merely restore a field of one.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        check(!st.account_exists(addr(9)), "13: absent to begin with");
        // The row must exist in current_ BEFORE the frame opens. A mutator that creates it inside
        // the frame gets a Created record, and Created erases the whole row on reject -- which
        // restores the value by accident and makes the narrow record below untestable.
        // access_account leaves account_ absent, which is what this case needs.
        st.access_account(addr(9));
        st.push();
        st.set_nonce(addr(9), 5);
        check(st.account_exists(addr(9)), "13: the mutator materialised it");
        check(st.get_nonce(addr(9)) == 5, "13: and wrote the field");
        st.pop_reject();
        check(!st.account_exists(addr(9)), "13: reject leaves NO account, not an empty one");
    }

    current_case = 14;
    // ---- 14. PageTracker: update_page in a frame that reverts.
    // Nothing else reaches this. access_page and update_page sit behind
    // `if constexpr (traits::mip_8_active())`, which is false on the Ethereum traits, so neither the
    // corpus nor any other case here exercises the Pages record. State::update_page is not
    // templated, so this calls it directly and the record is tested on its own terms.
    {
        StubDb db;
        db.put_account(1, Account{.nonce = 1});
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        // The row must exist in current_ BEFORE the frame opens. A mutator that creates it inside
        // the frame gets a Created record, and Created erases the whole row on reject -- which
        // restores the value by accident and makes the narrow record below untestable.
        st.access_account(addr(1));
        st.push();
        auto const first = st.update_page(addr(1), key(5), EVMC_STORAGE_ADDED);
        st.pop_reject();
        st.push();
        auto const again = st.update_page(addr(1), key(5), EVMC_STORAGE_ADDED);
        check(again.first_page_write == first.first_page_write &&
                  again.grew_state == first.grew_state,
              "14: after a reject the page map is as it was, so the same update answers the same");
        st.pop_accept();
    }

    current_case = 15;
    // ---- 15. incarnation changed on an account that ALREADY exists, then rejected.
    // Case 13 covers the other half of AccountWhole -- an account appearing. This is the half where
    // the account was already there and only its incarnation moved, which no narrow record can say.
    {
        StubDb db;
        db.put_account(1, Account{.balance = 5, .code_hash = NULL_HASH, .nonce = 0});
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{1, 0}};
        check(!st.is_current_incarnation(addr(1)), "15: a foreign incarnation to begin with");
        // The row must exist in current_ BEFORE the frame opens. A mutator that creates it inside
        // the frame gets a Created record, and Created erases the whole row on reject -- which
        // restores the value by accident and makes the narrow record below untestable.
        st.access_account(addr(1));
        st.push();
        st.set_to_state_incarnation(addr(1));
        check(st.is_current_incarnation(addr(1)), "15: moved to this state's incarnation");
        st.pop_reject();
        check(!st.is_current_incarnation(addr(1)), "15: reject puts the old incarnation back");
        check(st.get_balance(addr(1)) == 5, "15: and leaves the rest of the account alone");
    }

    return failures;
}
