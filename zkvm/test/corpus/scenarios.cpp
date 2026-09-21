// Copyright (C) 2026 Category Labs, Inc.
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

#include <zkvm/test/corpus/contracts/namespace_spoke_bytecode.hpp>
#include <zkvm/test/corpus/scenarios.hpp>
#include <zkvm/test/corpus/tx_sign.hpp>

#include <category/core/assert.h>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/state3/state.hpp>

#include <cstddef>
#include <cstring>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

using namespace monad;

byte_string hex(std::string_view const s)
{
    MONAD_ASSERT(s.size() % 2 == 0);
    byte_string out;
    out.reserve(s.size() / 2);
    for (size_t i = 0; i < s.size(); i += 2) {
        auto const hi = from_hex_char(s[i]);
        auto const lo = from_hex_char(s[i + 1]);
        MONAD_ASSERT(hi.has_value() && lo.has_value());
        out.push_back(
            static_cast<unsigned char>((hi.value() << 4) | lo.value()));
    }
    return out;
}

/// Right-aligned 32-byte word, the ABI's only shape for a scalar.
void push_word(byte_string &out, uint256_t const &v)
{
    auto const w = store_be_as<bytes32_t>(v);
    out.append(w.bytes, sizeof(w.bytes));
}

void push_word(byte_string &out, Address const &a)
{
    out.append(12, 0);
    out.append(a.bytes, sizeof(a.bytes));
}

/// A dynamic `bytes` argument: the head carries an offset, the tail the length
/// then the payload padded to a word.
byte_string abi_call_address_bytes(
    byte_string_view selector, Address const &to, byte_string_view payload)
{
    byte_string out{selector};
    push_word(out, to);
    push_word(out, uint256_t{0x40}); // two head words precede the tail
    push_word(out, uint256_t{payload.size()});
    out.append(payload);
    if (auto const rem = payload.size() % 32; rem != 0) {
        out.append(32 - rem, 0);
    }
    return out;
}

// --- hand-assembled runtime code, the idiom execute_transaction_test uses ---

/// No calldata: set slots 0,1,2. Any calldata: zero slot 1, which collapses a
/// storage branch -- the case the witness has to cover with a Digest.
///
///   CALLDATASIZE ISZERO PUSH1 0x0b JUMPI
///   PUSH1 0 PUSH1 1 SSTORE STOP
///   JUMPDEST PUSH1 1 PUSH1 0 SSTORE  PUSH1 2 PUSH1 1 SSTORE
///            PUSH1 3 PUSH1 2 SSTORE  STOP
constexpr std::string_view STORE_CODE = "3615600b57"
                                        "60006001"
                                        "55"
                                        "00"
                                        "5b"
                                        "60016000"
                                        "55"
                                        "60026001"
                                        "55"
                                        "60036002"
                                        "55"
                                        "00";

/// PUSH1 0x42 PUSH1 0x20 PUSH1 0 LOG1 STOP -- one log, one topic.
constexpr std::string_view LOG_CODE = "604260206000a100";

/// PUSH1 0 PUSH1 0 REVERT -- a receipt with status 0 and no state change.
constexpr std::string_view REVERT_CODE = "60006000fd";

/// CALLER SELFDESTRUCT. Paris is before EIP-6780, so this really destroys,
/// which is the account-deletion path in the witness.
constexpr std::string_view SELFDESTRUCT_CODE = "33ff";

/// Init code returning `PUSH1 0 PUSH1 0 SSTORE` as runtime: the five bytes go
/// in at memory 27 because MSTORE right-aligns a word.
constexpr std::string_view DEPLOY_INIT = "6460006000556000526005601bf3";

Address addr_of(bytes32_t const &k)
{
    return corpus::address_of(k);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

namespace corpus
{
    namespace
    {
        constexpr uint256_t FUND = 100'000'000'000'000'000; // 0.1 ether
        constexpr uint64_t MAX_FEE = 100;
        constexpr uint64_t PRIORITY_FEE = 1;

        Transaction call(
            std::optional<Address> to, uint64_t gas, uint256_t value,
            byte_string data, TransactionType type = TransactionType::eip1559)
        {
            Transaction tx{
                .max_fee_per_gas = MAX_FEE,
                .gas_limit = gas,
                .value = value,
                .to = to,
                .type = type,
                .data = std::move(data),
                .max_priority_fee_per_gas =
                    type == TransactionType::eip1559 ? PRIORITY_FEE : 0};
            if (type == TransactionType::legacy) {
                // A legacy transaction carries no priority fee, and gas_price
                // IS max_fee_per_gas.
                tx.max_priority_fee_per_gas = 0;
            }
            tx.sc.chain_id = 1;
            return tx;
        }
    }

    bytes32_t derive_key(bytes32_t const &seed, uint64_t const index)
    {
        byte_string buf{seed.bytes, sizeof(seed.bytes)};
        unsigned char be[8];
        for (unsigned i = 0; i < 8; ++i) {
            be[i] = static_cast<unsigned char>(index >> (56 - 8 * i));
        }
        buf.append(be, sizeof(be));
        auto k = to_bytes(keccak256(buf));
        // Vanishingly unlikely, but a zero scalar is not a key and the signer
        // would abort rather than tell you why.
        MONAD_ASSERT(k != bytes32_t{});
        return k;
    }

    std::vector<Scenario> all_scenarios(bytes32_t const &seed)
    {
        std::vector<Scenario> out;

        // ------------------------------------------------------------------
        // transfers + storage
        // ------------------------------------------------------------------
        {
            std::vector<bytes32_t> keys;
            for (uint64_t i = 0; i < 20; ++i) {
                keys.push_back(derive_key(seed, i));
            }
            Address const store_addr =
                0x00000000000000000000000000000000000c0de1_address;

            Scenario s;
            s.name = "transfers";
            s.genesis = [keys, store_addr](State &st) {
                for (auto const &k : keys) {
                    st.add_to_balance(addr_of(k), FUND);
                }
                st.create_contract(store_addr);
                st.set_code(store_addr, hex(STORE_CODE));
            };
            s.blocks = [keys, store_addr](CorpusBuilder &) {
                std::vector<BlockSpec> blocks;

                // 1: a ring of transfers, every account both sender and payee.
                BlockSpec b1;
                for (size_t i = 0; i < keys.size(); ++i) {
                    b1.txs.push_back(call(
                        addr_of(keys[(i + 1) % keys.size()]),
                        21'000,
                        1'000 + i,
                        {}));
                    b1.keys.push_back(keys[i]);
                }
                blocks.push_back(std::move(b1));

                // 2: fill the contract's slots, then zero one of them in the
                // same block -- the collapse happens inside one witness.
                BlockSpec b2;
                b2.txs.push_back(call(store_addr, 100'000, 0, {}));
                b2.keys.push_back(keys[0]);
                b2.txs.push_back(call(store_addr, 100'000, 0, hex("01")));
                b2.keys.push_back(keys[1]);
                blocks.push_back(std::move(b2));

                return blocks;
            };
            out.push_back(std::move(s));
        }

        // ------------------------------------------------------------------
        // broad EVM coverage
        // ------------------------------------------------------------------
        {
            std::vector<bytes32_t> keys;
            for (uint64_t i = 100; i < 110; ++i) {
                keys.push_back(derive_key(seed, i));
            }
            Address const log_addr =
                0x00000000000000000000000000000000000c0de2_address;
            Address const revert_addr =
                0x00000000000000000000000000000000000c0de3_address;
            Address const suicide_addr =
                0x00000000000000000000000000000000000c0de4_address;

            Scenario s;
            s.name = "evm";
            s.genesis = [keys, log_addr, revert_addr, suicide_addr](State &st) {
                for (auto const &k : keys) {
                    st.add_to_balance(addr_of(k), FUND);
                }
                st.create_contract(log_addr);
                st.set_code(log_addr, hex(LOG_CODE));
                st.create_contract(revert_addr);
                st.set_code(revert_addr, hex(REVERT_CODE));
                st.create_contract(suicide_addr);
                st.set_code(suicide_addr, hex(SELFDESTRUCT_CODE));
                // A balance to move on destruction, so the deletion is not a
                // no-op for the accounts trie.
                st.add_to_balance(suicide_addr, 12'345);
            };
            s.blocks = [keys, log_addr, revert_addr, suicide_addr](
                           CorpusBuilder &) {
                std::vector<BlockSpec> blocks;

                BlockSpec b1;
                // CREATE
                b1.txs.push_back(
                    call(std::nullopt, 200'000, 0, hex(DEPLOY_INIT)));
                b1.keys.push_back(keys[0]);
                // a log
                b1.txs.push_back(call(log_addr, 100'000, 0, {}));
                b1.keys.push_back(keys[1]);
                // a revert: status 0, gas spent, no state change
                b1.txs.push_back(call(revert_addr, 100'000, 0, {}));
                b1.keys.push_back(keys[2]);
                // legacy and 2930 alongside 1559
                b1.txs.push_back(call(
                    addr_of(keys[4]), 21'000, 5, {}, TransactionType::legacy));
                b1.keys.push_back(keys[3]);
                b1.txs.push_back(call(
                    addr_of(keys[5]), 21'000, 5, {}, TransactionType::eip2930));
                b1.keys.push_back(keys[4]);
                blocks.push_back(std::move(b1));

                // 2: destroy an account with a balance.
                BlockSpec b2;
                b2.txs.push_back(call(suicide_addr, 100'000, 0, {}));
                b2.keys.push_back(keys[6]);
                blocks.push_back(std::move(b2));

                return blocks;
            };
            out.push_back(std::move(s));
        }

        // ------------------------------------------------------------------
        // the real NamespaceSpoke
        // ------------------------------------------------------------------
        {
            std::vector<bytes32_t> keys;
            for (uint64_t i = 200; i < 205; ++i) {
                keys.push_back(derive_key(seed, i));
            }

            Scenario s;
            s.name = "spoke";
            s.genesis = [keys](State &st) {
                for (auto const &k : keys) {
                    st.add_to_balance(addr_of(k), FUND);
                }
            };
            s.blocks = [keys](CorpusBuilder &b) {
                std::vector<BlockSpec> blocks;

                // 1: deploy it. The constructor takes (uint64 chainId,
                // address operator) and writes both into the runtime code as
                // immutables, which is why this is a CREATE and not a seeded
                // account.
                byte_string init = hex(NAMESPACE_SPOKE_CREATION_HEX);
                push_word(init, uint256_t{1});
                push_word(init, addr_of(keys[0]));

                Address const spoke = b.next_contract_address(addr_of(keys[0]));

                BlockSpec b1;
                b1.txs.push_back(call(std::nullopt, 2'000'000, 0, init));
                b1.keys.push_back(keys[0]);
                blocks.push_back(std::move(b1));

                // 2: three outbound messages. Each pushes into
                // _pendingNamespaceMessages (slot 1) and emits
                // NamespaceMessageRecorded, which is what the anchor harvests.
                BlockSpec b2;
                for (size_t i = 1; i < 4; ++i) {
                    byte_string payload;
                    payload.append(i * 5, static_cast<unsigned char>(0xa0 + i));
                    b2.txs.push_back(call(
                        spoke,
                        300'000,
                        0,
                        abi_call_address_bytes(
                            hex("acc30635"), addr_of(keys[i]), payload)));
                    b2.keys.push_back(keys[i]);
                }
                blocks.push_back(std::move(b2));

                return blocks;
            };
            out.push_back(std::move(s));
        }

        return out;
    }
}

MONAD_NAMESPACE_END
