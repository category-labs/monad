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

    return failures;
}
