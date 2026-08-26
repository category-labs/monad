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

#include <cstdio>
#include <map>

using namespace monad;

namespace
{
    int failures = 0;

    void check(bool ok, char const *what)
    {
        if (!ok) {
            std::printf("  FAIL  %s\n", what);
            ++failures;
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
        std::map<unsigned char, Account> accounts;
        std::map<std::pair<unsigned char, unsigned char>, bytes32_t> storage;

        bool is_page_encoded() const override { return false; }

        std::optional<Account> read_account(Address const &a) override
        {
            auto const it = accounts.find(a.bytes[19]);
            if (it == accounts.end()) {
                return std::nullopt;
            }
            return it->second;
        }

        bytes32_t read_storage(
            Address const &a, Incarnation, bytes32_t const &k) override
        {
            auto const it = storage.find({a.bytes[19], k.bytes[31]});
            return it == storage.end() ? bytes32_t{} : it->second;
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
    };
}

int main()
{
    std::printf("revert semantics\n");

    // ---- 1. parent writes, child ACCEPTS, parent REJECTS.
    // The record the child left behind carries the pre-PARENT value, so the parent's own write
    // must disappear too. This is the case the corpus covers 89,826 times; asserted here because
    // the reasoning it rests on -- a row the child was first to touch was untouched by the parent
    // -- is the one thing that makes leaving records to the parent correct.
    {
        StubDb db;
        db.accounts[1] = Account{.nonce = 7};
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

    // ---- 2. parent writes, child REJECTS, parent ACCEPTS.
    {
        StubDb db;
        db.accounts[1] = Account{.nonce = 7};
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

    // ---- 3. the same field written twice in one frame, then rejected.
    {
        StubDb db;
        db.accounts[1] = Account{.nonce = 7};
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

    // ---- 5. SELFDESTRUCT then revert. Zero occurrences in the corpus.
    {
        StubDb db;
        db.accounts[1] = Account{.nonce = 1, .balance = 500};
        db.accounts[3] = Account{.nonce = 0};
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        st.push();
        st.selfdestruct<EvmTraits<EVMC_SHANGHAI>>(addr(1), addr(3));
        check(st.is_destructed(addr(1)), "5: destructed inside the frame");
        st.pop_reject();
        check(!st.is_destructed(addr(1)), "5: reject clears the destruct flag");
        check(st.get_balance(addr(1)) == 500, "5: and gives the balance back");
    }

    // ---- 6. storage and transient storage.
    {
        StubDb db;
        db.accounts[1] = Account{.nonce = 1};
        db.storage[{1, 5}] = key(42);
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        st.push();
        st.set_storage<EvmTraits<EVMC_SHANGHAI>>(addr(1), key(5), key(99));
        st.set_transient_storage(addr(1), key(6), key(77));
        check(st.get_storage(addr(1), key(5)) == key(99), "6: storage written");
        check(st.get_transient_storage(addr(1), key(6)) == key(77), "6: transient written");
        st.pop_reject();
        check(st.get_storage(addr(1), key(5)) == key(42), "6: storage reverts to the db value");
        check(st.get_transient_storage(addr(1), key(6)) == bytes32_t{}, "6: transient reverts to empty");
    }

    // ---- 7. EIP-2929: a key warmed in a frame that reverts must be cold again.
    {
        StubDb db;
        db.accounts[1] = Account{.nonce = 1};
        vm::VM vm;
        BlockState bs{db, vm};
        State st{bs, Incarnation{0, 0}};
        st.push();
        check(st.access_account(addr(1)) == EVMC_ACCESS_COLD, "7: account cold first");
        check(st.access_account(addr(1)) == EVMC_ACCESS_WARM, "7: then warm");
        check(st.access_storage<EvmTraits<EVMC_SHANGHAI>>(addr(1), key(5)) == EVMC_ACCESS_COLD,
              "7: slot cold first");
        check(st.access_storage<EvmTraits<EVMC_SHANGHAI>>(addr(1), key(5)) == EVMC_ACCESS_WARM,
              "7: then warm");
        st.pop_reject();
        st.push();
        check(st.access_account(addr(1)) == EVMC_ACCESS_COLD, "7: account COLD again after reject");
        check(st.access_storage<EvmTraits<EVMC_SHANGHAI>>(addr(1), key(5)) == EVMC_ACCESS_COLD,
              "7: slot COLD again after reject");
        st.pop_accept();
    }

    if (failures == 0) {
        std::printf("  all cases pass\n");
        return 0;
    }
    std::printf("  %d failed\n", failures);
    return 1;
}
