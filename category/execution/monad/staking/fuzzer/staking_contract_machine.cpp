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

#include <category/execution/monad/staking/fuzzer/staking_contract_machine.hpp>
#include <category/execution/monad/staking/test/input_generation.hpp>
#include <category/execution/monad/staking/util/bls.hpp>
#include <category/execution/monad/staking/util/secp256k1.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <algorithm>

using namespace monad;
using namespace monad::staking::test;
using namespace monad::staking::test::fuzzing;
using namespace monad::vm::fuzzing;

namespace
{
    byte_string_view
    consume_bytes(byte_string_view &data, size_t const num_bytes)
    {
        byte_string_view ret = data.substr(0, num_bytes);
        data.remove_prefix(num_bytes);
        return ret;
    }
}

namespace monad::staking::test
{
    template <Traits traits>
    StakingContractMachine<traits>::StakingContractMachine(
        seed_t seed, Config const &config)
        : engine_{seed}
        , enable_pubkey_assertions_{config.enable_pubkey_assertions}
        , enable_trace_{config.enable_trace}
    {
        assert_all_invariants();
        MONAD_ASSERT(
            config.close_to_max_active_validators_prob >= 0 &&
            config.close_to_max_active_validators_prob <= 1);
        MONAD_ASSERT(
            config.many_active_validators_prob >= 0 &&
            config.many_active_validators_prob <= 1);

        constexpr size_t max_initial_active_vals = 260;

        // The max initial active validators must be able to fill up
        // a bitset bucket:
        static_assert(max_initial_active_vals >= 256);

        // The fuzzer starts to become slow when the initial active valset
        // size becomes too big:
        static_assert(ACTIVE_VALSET_SIZE - 1 <= max_initial_active_vals);

        discrete_choice<int>(
            engine_,
            [](auto &) { return 0; },
            Choice(
                config.close_to_max_active_validators_prob,
                [&, this](auto &) {
                    std::cout << "Spam insert " << (ACTIVE_VALSET_SIZE - 1)
                              << " "
                              << "active validators, close to maximum active"
                              << std::endl;
                    for (size_t i = 1; i < ACTIVE_VALSET_SIZE; ++i) {
                        auto const [signer, msg, secp, bls, sender, value] =
                            gen_precompile_add_validator_input(
                                ACTIVE_VALIDATOR_STAKE, MAX_STAKE);
                        model_precompile_add_validator(
                            signer, msg, secp, bls, sender, value);
                        assert_all_invariants();
                    }
                    MONAD_ASSERT(
                        model_.valset_execution().length() ==
                        ACTIVE_VALSET_SIZE - 1);
                    return 0;
                }),
            Choice(config.many_active_validators_prob, [&, this](auto &) {
                std::cout << "Spam insert " << max_initial_active_vals << " "
                          << "active validators, to fill up a bitset bucket"
                          << std::endl;
                for (size_t i = 0; i < max_initial_active_vals; ++i) {
                    auto const [signer, msg, secp, bls, sender, value] =
                        gen_precompile_add_validator_input(
                            ACTIVE_VALIDATOR_STAKE, MAX_STAKE);
                    model_precompile_add_validator(
                        signer, msg, secp, bls, sender, value);
                    assert_all_invariants();
                }
                MONAD_ASSERT(
                    model_.valset_execution().length() ==
                    max_initial_active_vals);
                return 0;
            }));

        assert_all_invariants();
    }

    template <Traits traits>
    void StakingContractMachine<traits>::assert_all_invariants()
    {
        assert_valset_invariants();
        assert_val_execution_invariants();
        assert_delegator_invariants();
        assert_accumulated_rewards_invariants();
        assert_linked_list_invariants();
        assert_solvency_invariants();
    }

    template <Traits traits>
    void StakingContractMachine<traits>::assert_valset_invariants()
    {
        std::unordered_set<uint64_t> valset_execution;
        auto model_valset_execution = model_.valset_execution();
        auto const valset_execution_length = model_valset_execution.length();
        for (uint64_t i = 0; i < valset_execution_length; ++i) {
            auto const v = model_valset_execution.get(i).load().native();
            valset_execution.insert(v);
        }

        std::unordered_set<uint64_t> valset_snapshot;
        auto model_valset_snapshot = model_.valset_snapshot();
        auto const valset_snapshot_length = model_valset_snapshot.length();
        for (uint64_t i = 0; i < valset_snapshot_length; ++i) {
            auto const v = model_valset_snapshot.get(i).load().native();
            valset_snapshot.insert(v);
        }

        std::unordered_set<uint64_t> valset_consensus;
        auto model_valset_consensus = model_.valset_consensus();
        auto const valset_consensus_length = model_valset_consensus.length();
        for (uint64_t i = 0; i < valset_consensus_length; ++i) {
            auto const v = model_valset_consensus.get(i).load().native();
            valset_consensus.insert(v);
        }

        // pairwise distinct elements:
        MONAD_ASSERT(valset_execution.size() == valset_execution_length);

        for (uint64_t v : valset_execution) {
            MONAD_ASSERT(model_.val_execution(v).auth_address() != Address{});
        }

        // pairwise distinct elements:
        MONAD_ASSERT(valset_consensus.size() == valset_consensus_length);

        MONAD_ASSERT(valset_consensus_length <= ACTIVE_VALSET_SIZE);

        // pairwise distinct elements:
        MONAD_ASSERT(valset_snapshot.size() == valset_snapshot_length);

        MONAD_ASSERT(valset_snapshot_length <= ACTIVE_VALSET_SIZE);

        for (uint64_t v : valset_consensus) {
            MONAD_ASSERT(valset_execution.contains(v));
        }

        for_all_val_ids([&, this](u64_be v) {
            MONAD_ASSERT(
                valset_consensus.contains(v.native()) ==
                (model_.consensus_view(v).stake().load().native() >=
                 ACTIVE_VALIDATOR_STAKE));

            MONAD_ASSERT(
                valset_snapshot.contains(v.native()) ==
                (model_.snapshot_view(v).stake().load().native() >=
                 ACTIVE_VALIDATOR_STAKE));

            MONAD_ASSERT(
                model_.consensus_view(v).commission().load().native() <=
                MAX_COMMISSION);

            MONAD_ASSERT(
                model_.snapshot_view(v).commission().load().native() <=
                MAX_COMMISSION);

            auto const bit_bucket = model_.val_bitset_bucket(v).load().native();
            MONAD_ASSERT(
                !!(bit_bucket & (uint256_t{1} << (v.native() & 255))) ==
                valset_execution.contains(v.native()));

            auto const current_stake =
                model_.val_execution(v).stake().load().native();
            auto const auth_stake =
                model_.delegator(v, model_.val_execution(v).auth_address())
                    .stake()
                    .load()
                    .native();
            MONAD_ASSERT(
                current_stake < ACTIVE_VALIDATOR_STAKE ||
                auth_stake < MIN_VALIDATE_STAKE ||
                valset_execution.contains(v.native()));

            if (!model_.in_epoch_delay_period()) {
                MONAD_ASSERT(
                    model_.active_consensus_stake(v) ==
                    model_.consensus_view(v).stake().load().native());
                MONAD_ASSERT(
                    model_.active_consensus_commission(v) ==
                    model_.consensus_view(v).commission().load().native());
            }
            else {
                MONAD_ASSERT(
                    model_.active_consensus_stake(v) ==
                    model_.snapshot_view(v).stake().load().native());
                MONAD_ASSERT(
                    model_.active_consensus_commission(v) ==
                    model_.snapshot_view(v).commission().load().native());
            }
        });
    }

    template <Traits traits>
    void StakingContractMachine<traits>::assert_val_execution_invariants()
    {
        for_all_val_ids([&, this](u64_be v) {
            MONAD_ASSERT(
                (v.native() == 0 || v.native() > model_.last_val_id()) ||
                model_.val_execution(v).auth_address() != Address{});

            MONAD_ASSERT(
                (v.native() > 0 && v.native() <= model_.last_val_id()) ||
                model_.val_execution(0).auth_address() == Address{});

            MONAD_ASSERT(
                v.native() == 0 ||
                model_.val_execution(v.native() + 1).auth_address() ==
                    Address{} ||
                model_.val_execution(v).auth_address() != Address{});

            auto const auth_address = model_.val_execution(v).auth_address();
            auto const stake_sum =
                model_.delegator(v, auth_address).stake().load().native() +
                model_.delegator(v, auth_address)
                    .delta_stake()
                    .load()
                    .native() +
                model_.delegator(v, auth_address)
                    .next_delta_stake()
                    .load()
                    .native();
            MONAD_ASSERT(
                (v.native() == 0 || v.native() > model_.last_val_id()) ||
                (stake_sum >= MIN_VALIDATE_STAKE) ==
                    !(model_.val_execution(v).get_flags() &
                      ValidatorFlagWithdrawn));

            MONAD_ASSERT(
                model_.val_execution(v).commission().load().native() <=
                MAX_COMMISSION);

            MONAD_ASSERT(model_.val_execution(v).get_flags() < 4);

            MONAD_ASSERT(
                (v.native() == 0 || v.native() > model_.last_val_id()) ||
                (model_.val_execution(v).stake().load().native() >=
                 ACTIVE_VALIDATOR_STAKE) ==
                    !(model_.val_execution(v).get_flags() &
                      ValidatorFlagsStakeTooLow));

            if (enable_pubkey_assertions_) {
                auto const keys = model_.val_execution(v).keys().load();

                Secp256k1Pubkey const secp_pubkey{keys.secp_pubkey};
                if (secp_pubkey.is_valid()) {
                    MONAD_ASSERT(
                        v.native() > 0 && v.native() <= model_.last_val_id());
                    auto const secp_eth_address =
                        address_from_secpkey(secp_pubkey.serialize());
                    MONAD_ASSERT(model_.val_id(secp_eth_address) != 0);
                }
                else {
                    MONAD_ASSERT(
                        v.native() == 0 || v.native() > model_.last_val_id());
                }

                BlsPubkey const bls_pubkey{keys.bls_pubkey};
                if (bls_pubkey.is_valid()) {
                    MONAD_ASSERT(
                        v.native() > 0 && v.native() <= model_.last_val_id());
                    auto const bls_eth_address =
                        address_from_bls_key(bls_pubkey.serialize());
                    MONAD_ASSERT(model_.val_id_bls(bls_eth_address) != 0);
                }
                else {
                    MONAD_ASSERT(
                        v.native() == 0 || v.native() > model_.last_val_id());
                }
            }
        });
    }

    template <Traits traits>
    void StakingContractMachine<traits>::assert_delegator_invariants()
    {
        for_all_val_ids_and_addresses([&, this](u64_be v, Address const &a) {
            auto del = model_.delegator(v, a);

            MONAD_ASSERT(
                del.next_delta_stake().load().native() == 0 ||
                del.next_delta_stake().load().native() >= DUST_THRESHOLD);

            MONAD_ASSERT(
                del.delta_stake().load().native() == 0 ||
                del.delta_stake().load().native() >= DUST_THRESHOLD);

            MONAD_ASSERT(
                del.stake().load().native() == 0 ||
                del.stake().load().native() >= DUST_THRESHOLD);

            MONAD_ASSERT(
                (del.next_delta_stake().load().native() == 0) ==
                (del.get_next_delta_epoch().native() == 0));

            MONAD_ASSERT(
                (del.delta_stake().load().native() == 0) ==
                (del.get_delta_epoch().native() == 0));

            MONAD_ASSERT(
                del.get_delta_epoch().native() == 0 ||
                del.get_next_delta_epoch().native() == 0 ||
                del.get_next_delta_epoch().native() ==
                    del.get_delta_epoch().native() + 1);

            MONAD_ASSERT(del.get_delta_epoch().native() <= model_.epoch() + 1);

            MONAD_ASSERT(
                del.get_next_delta_epoch().native() <= model_.epoch() + 2);

            auto const &withdrawal_ids = model_.active_withdrawal_ids(v, a);

            // The invariant
            // withdrawal_request.amount = 0 iff withdrawal_request.epoch = 0
            // is slowing slowing down the invariant checking too much.
            // Instead just verify that the known withdrawal requests have
            // non-zero epoch and value.
            for (uint8_t const i : withdrawal_ids) {
                MONAD_ASSERT(
                    model_.withdrawal_request(v, a, i).load().amount.native() >
                    0);
                MONAD_ASSERT(
                    model_.withdrawal_request(v, a, i).load().epoch.native() >
                    0);

                // This is not part of the properties document.
                // It is used to sanity check the machine:
                std::tuple<uint64_t, Address, uint8_t> const key = {
                    v.native(), a, i};
                MONAD_ASSERT(all_withdrawal_requests_.contains(key));
            }

            auto const error_bound = model_.error_bound() + 3 + 256;
            auto const unit_bias_rewards = model_.unit_bias_rewards(v, a);
            auto const pending_rewards = model_.pending_rewards(v, a);
            auto const active_rewards =
                model_.delegator(v, a).rewards().load().native() +
                pending_rewards;
            MONAD_ASSERT(
                unit_bias_rewards <=
                (active_rewards + error_bound) * UNIT_BIAS);
            MONAD_ASSERT(
                (active_rewards + error_bound) * UNIT_BIAS <=
                unit_bias_rewards + (error_bound * UNIT_BIAS));

            auto const this_epoch = model_.epoch();

            auto actual_delegator_stake = del.stake().load().native();
            if (del.get_delta_epoch().native() <= this_epoch) {
                actual_delegator_stake += del.delta_stake().load().native();
            }
            if (del.get_next_delta_epoch().native() <= this_epoch) {
                actual_delegator_stake +=
                    del.next_delta_stake().load().native();
            }
            MONAD_ASSERT(
                model_.delegator_stake(v, a, this_epoch) ==
                actual_delegator_stake);

            uint256_t actual_withdrawal_stake;
            for (uint8_t const i : withdrawal_ids) {
                auto withdrawal = model_.withdrawal_request(v, a, i).load();
                if (withdrawal.epoch.native() > this_epoch) {
                    actual_withdrawal_stake += withdrawal.amount.native();
                }
            }
            MONAD_ASSERT(
                model_.withdrawal_stake(v, a, this_epoch) ==
                actual_withdrawal_stake);
        });

        for_all_val_ids([&, this](u64_be v) {
            auto const epoch = model_.epoch();
            uint256_t del_stake_sum;
            uint256_t withdraw_stake_sum;
            for_all_addresses([&, this](Address const &a) {
                del_stake_sum += model_.delegator_stake(v, a, epoch);
                withdraw_stake_sum += model_.withdrawal_stake(v, a, epoch);
            });
            MONAD_ASSERT(
                model_.active_consensus_stake(v) == 0 ||
                model_.active_consensus_stake(v) ==
                    del_stake_sum + withdraw_stake_sum);
        });
    }

    template <Traits traits>
    void StakingContractMachine<traits>::assert_accumulated_rewards_invariants()
    {
        for_all_val_ids([&, this](u64_be v) {
            auto const begin_epoch = std::max(model_.epoch(), uint64_t{2}) - 2;
            for (uint64_t e = begin_epoch; e <= model_.epoch() + 4; ++e) {
                auto const refcount =
                    model_.accumulated_reward_per_token(e, v).refcount.native();
                uint256_t computed_refcount;
                for_all_addresses([&, this](Address const &a) {
                    auto del = model_.delegator(v, a);
                    if (e > 0 && del.get_delta_epoch().native() == e) {
                        computed_refcount += 1;
                    }
                    if (e > 0 && del.get_next_delta_epoch().native() == e) {
                        computed_refcount += 1;
                    }
                    auto const &withdrawal_ids =
                        model_.active_withdrawal_ids(v, a);
                    for (uint8_t const i : withdrawal_ids) {
                        auto withdrawal =
                            model_.withdrawal_request(v, a, u8_be{i}).load();
                        if (e > 0 && withdrawal.epoch.native() == e) {
                            computed_refcount += 1;
                        }
                    }
                });
                MONAD_ASSERT(refcount == computed_refcount);

                MONAD_ASSERT(
                    (e != 0 && e <= model_.epoch() + 2) || refcount == 0);

                auto const value =
                    model_.accumulated_reward_per_token(e, v).value.native();

                MONAD_ASSERT(refcount != 0 || value == 0);

                auto const next_refcount =
                    model_.accumulated_reward_per_token(e + 1, v)
                        .refcount.native();
                auto const next_value =
                    model_.accumulated_reward_per_token(e + 1, v)
                        .value.native();

                MONAD_ASSERT(next_refcount == 0 || value <= next_value);

                MONAD_ASSERT(
                    value <= model_.val_execution(v)
                                 .accumulated_reward_per_token()
                                 .load()
                                 .native());
            }

            for_all_addresses([&, this](Address const &a) {
                auto const &withdrawal_ids = model_.active_withdrawal_ids(v, a);
                for (uint8_t const i : withdrawal_ids) {
                    auto withdrawal =
                        model_.withdrawal_request(v, a, u8_be{i}).load();
                    auto const upper_acc =
                        model_.accumulated_reward_per_token(withdrawal.epoch, v)
                            .value.native();
                    MONAD_ASSERT(withdrawal.acc.native() <= upper_acc);
                }

                auto del = model_.delegator(v, a);
                auto val = model_.val_execution(v);
                MONAD_ASSERT(
                    del.accumulated_reward_per_token().load().native() <=
                    val.accumulated_reward_per_token().load().native());

                auto const delta_epoch = del.get_delta_epoch().native();
                if (delta_epoch > 0 && delta_epoch <= model_.epoch()) {
                    MONAD_ASSERT(
                        del.accumulated_reward_per_token().load().native() <=
                        model_.accumulated_reward_per_token(delta_epoch, v)
                            .value.native());
                }

                auto const nd_epoch = del.get_next_delta_epoch().native();
                if (nd_epoch > 0 && nd_epoch <= model_.epoch()) {
                    MONAD_ASSERT(
                        del.accumulated_reward_per_token().load().native() <=
                        model_.accumulated_reward_per_token(nd_epoch, v)
                            .value.native());

                    MONAD_ASSERT(
                        model_.accumulated_reward_per_token(delta_epoch, v)
                            .value.native() <=
                        model_.accumulated_reward_per_token(nd_epoch, v)
                            .value.native());
                }
            });
        });
    }

    template <Traits traits>
    void StakingContractMachine<traits>::assert_linked_list_invariants()
    {
        std::unordered_map<uint64_t, std::unordered_set<Address>> del_sets;
        for_all_val_ids([&, this](u64_be v) {
            auto const del_vec = model_.get_delegators_for_validator(v);
            auto &del_set = del_sets[v.native()];
            for (auto const a : del_vec) {
                auto const [_, ins] = del_set.insert(a);
                MONAD_ASSERT(ins);
            }
        });

        std::unordered_map<Address, std::unordered_set<uint64_t>> val_sets;
        for_all_addresses([&, this](Address const &a) {
            auto const val_vec = model_.get_validators_for_delegator(a);
            auto &val_set = val_sets[a];
            for (auto const v : val_vec) {
                auto const [_, ins] = val_set.insert(v.native());
                MONAD_ASSERT(ins);
            }
        });

        for_all_val_ids_and_addresses([&, this](u64_be v, Address const &a) {
            MONAD_ASSERT(
                del_sets[v.native()].contains(a) ==
                val_sets[a].contains(v.native()));

            auto del = model_.delegator(v, a);
            auto const stake_sum = del.stake().load().native() +
                                   del.delta_stake().load().native() +
                                   del.next_delta_stake().load().native();
            MONAD_ASSERT(del_sets[v.native()].contains(a) == (stake_sum > 0));
        });
    }

    template <Traits traits>
    void StakingContractMachine<traits>::assert_solvency_invariants()
    {
        uint256_t computed_balance;
        for_all_val_ids([&, this](u64_be v) {
            computed_balance += model_.val_execution(v).stake().load().native();
            computed_balance +=
                model_.val_execution(v).unclaimed_rewards().load().native();

            for_all_addresses([&, this](Address const &a) {
                computed_balance +=
                    model_.delegator(v, a).rewards().load().native();

                auto const &withdrawal_ids = model_.active_withdrawal_ids(v, a);
                for (uint8_t const i : withdrawal_ids) {
                    computed_balance += model_.withdrawal_request(v, a, i)
                                            .load()
                                            .amount.native();
                }
            });
        });

        MONAD_ASSERT(model_.balance_of(STAKING_CA) == computed_balance);

        uint256_t error_bound = model_.error_bound();
        for_all_val_ids_and_addresses([&, this](u64_be v, Address const &a) {
            auto const &withdrawal_ids = model_.active_withdrawal_ids(v, a);
            error_bound += withdrawal_ids.size();
            auto del = model_.delegator(v, a);
            auto const stake_sum = del.stake().load().native() +
                                   del.delta_stake().load().native() +
                                   del.next_delta_stake().load().native();
            if (stake_sum > 0) {
                error_bound += 3;
            }
        });
        for_all_val_ids([&, this](u64_be v) {
            uint256_t pending_rewards_sum;
            for_all_addresses([&, this](Address const &a) {
                pending_rewards_sum += model_.pending_rewards(v, a);
            });
            MONAD_ASSERT(
                pending_rewards_sum <=
                model_.val_execution(v).unclaimed_rewards().load().native());

            MONAD_ASSERT(
                model_.val_execution(v).unclaimed_rewards().load().native() <=
                pending_rewards_sum + error_bound);
        });

        for_all_val_ids([&, this](u64_be v) {
            uint256_t stake_sum;
            for_all_addresses([&, this](Address const &a) {
                auto del = model_.delegator(v, a);
                stake_sum += del.stake().load().native();
                stake_sum += del.delta_stake().load().native();
                stake_sum += del.next_delta_stake().load().native();
            });
            MONAD_ASSERT(
                model_.val_execution(v).stake().load().native() == stake_sum);
        });
    }

    template <Traits traits>
    void StakingContractMachine<traits>::for_all_val_ids(
        std::function<void(u64_be)> f)
    {
        uint64_t n = model_.last_val_id() + 3;
        for (uint64_t i = 0; i < n; ++i) {
            f(i);
        }
    }

    template <Traits traits>
    void StakingContractMachine<traits>::for_all_addresses(
        std::function<void(Address const &)> f)
    {
        for (auto const &a : all_addresses_) {
            f(a);
        }
    }

    template <Traits traits>
    void StakingContractMachine<traits>::for_all_val_ids_and_addresses(
        std::function<void(u64_be, Address const &)> f)
    {
        for_all_val_ids([&](u64_be v) {
            for_all_addresses([&](Address const &a) { f(v, a); });
        });
    }

    template <Traits traits>
    bool StakingContractMachine<traits>::transition(Transition t)
    {
        if (enable_trace_) {
            std::cout << magic_enum::enum_name(t) << std::endl;
        }
        bool ok = true;
        switch (t) {
        case Transition::syscall_on_epoch_change:
            syscall_on_epoch_change();
            break;
        case Transition::syscall_snapshot:
            syscall_snapshot();
            break;
        case Transition::syscall_reward:
            syscall_reward();
            break;
        case Transition::precompile_add_validator:
            precompile_add_validator();
            break;
        case Transition::precompile_delegate:
            precompile_delegate();
            break;
        case Transition::precompile_undelegate:
            precompile_undelegate();
            break;
        case Transition::precompile_compound:
            ok = precompile_compound();
            break;
        case Transition::precompile_withdraw:
            ok = precompile_withdraw();
            break;
        case Transition::precompile_claim_rewards:
            precompile_claim_rewards();
            break;
        case Transition::precompile_change_commission:
            precompile_change_commission();
            break;
        case Transition::precompile_external_reward:
            ok = precompile_external_reward();
            break;
        case Transition::precompile_get_delegator:
            precompile_get_delegator();
            break;
        }
        // Skip `WITHDRAWAL_DELAY` epochs once in a while to allow for
        // withdrawal requests become ready in a more natural way than
        // skipping epochs immediately before the withdrawal.
        with_probability(
            engine_, 0.20, [&](auto &) { skip_epochs(WITHDRAWAL_DELAY); });
        assert_all_invariants();
        return ok;
    }

    template <Traits traits>
    void StakingContractMachine<traits>::skip_epochs(uint64_t const n)
    {
        if (n == 0) {
            return;
        }
        size_t i = 0;
        auto epoch = model_.epoch();
        if (epoch == 0 || model_.in_epoch_delay_period()) {
            ++i;
            auto const res = model_.syscall_on_epoch_change(++epoch);
            MONAD_ASSERT(res.has_value());
        }
        for (; i < n; ++i) {
            auto const res1 = model_.syscall_snapshot();
            MONAD_ASSERT(res1.has_value());
            auto const res2 = model_.syscall_on_epoch_change(++epoch);
            MONAD_ASSERT(res2.has_value());
        }
    }

    template <Traits traits>
    seed_t StakingContractMachine<traits>::gen()
    {
        return engine_();
    }

    template <Traits traits>
    StakingContractMachine<traits>::Transition
    StakingContractMachine<traits>::gen_transition()
    {
        auto const x = gen() % static_cast<seed_t>(TRANSITION_COUNT);
        return static_cast<Transition>(x);
    }

    template <Traits traits>
    Address StakingContractMachine<traits>::gen_new_address()
    {
        auto const x = gen_uint256();
        Address a;
        std::memcpy(a.bytes, intx::as_bytes(x), sizeof(a.bytes));
        all_addresses_.push_back(a);
        return a;
    }

    template <Traits traits>
    Address StakingContractMachine<traits>::gen_old_address()
    {
        MONAD_ASSERT(!all_addresses_.empty());
        return all_addresses_[gen() % all_addresses_.size()];
    }

    template <Traits traits>
    Address StakingContractMachine<traits>::gen_new_or_old_address()
    {
        if (all_addresses_.empty()) {
            return gen_new_address();
        }
        return discrete_choice<Address>(
            engine_,
            [this](auto &) { return gen_new_address(); },
            Choice(0.80, [this](auto &) { return gen_old_address(); }));
    }

    template <Traits traits>
    std::pair<u64_be, Address>
    StakingContractMachine<traits>::gen_validator_auth_address()
    {
        auto const &v = validator_auth_addresses_;
        if (v.empty()) {
            auto const [signer, msg, secp, bls, sender, value] =
                gen_precompile_add_validator_input(
                    MIN_VALIDATE_STAKE, MAX_STAKE);
            model_precompile_add_validator(
                signer, msg, secp, bls, sender, value);
            MONAD_ASSERT(!validator_auth_addresses_.empty());
        }
        return validator_auth_addresses_
            [gen() % validator_auth_addresses_.size()];
    }

    template <Traits traits>
    u64_be StakingContractMachine<traits>::gen_delegable_val_id()
    {
        if (!delegable_val_ids_.empty()) {
            auto const v = delegable_val_ids_.sample(engine_);
            MONAD_ASSERT(model_.val_execution(v).exists());
            return v;
        }
        auto const [signer, msg, secp, bls, sender, value] =
            gen_precompile_add_validator_input(
                MIN_VALIDATE_STAKE, MAX_DELEGABLE_STAKE);
        auto const v = model_precompile_add_validator(
            signer, msg, secp, bls, sender, value);
        MONAD_ASSERT(model_.val_execution(v).exists());
        return v;
    }

    template <Traits traits>
    u64_be StakingContractMachine<traits>::gen_potential_val_id()
    {
        if (all_val_ids_.empty()) {
            return gen();
        }
        return discrete_choice<u64_be>(
            engine_,
            [this](auto &) { return gen(); },
            Choice(0.50, [this](auto &) {
                return all_val_ids_[gen() % all_val_ids_.size()];
            }));
    }

    template <Traits traits>
    std::pair<u64_be, Address> StakingContractMachine<traits>::gen_delegator()
    {
        if (all_delegators_.empty()) {
            auto const [signer, msg, secp, bls, sender, value] =
                gen_precompile_add_validator_input(
                    MIN_VALIDATE_STAKE, MAX_STAKE);
            model_precompile_add_validator(
                signer, msg, secp, bls, sender, value);
            MONAD_ASSERT(!all_delegators_.empty());
        }
        auto const &[v, a] = all_delegators_.sample(engine_);
        return {u64_be{v}, a};
    }

    template <Traits traits>
    uint256_t StakingContractMachine<traits>::gen_uint256()
    {
        return uint256_t{gen(), gen(), gen(), gen()};
    }

    // Generate a random uint256 in the range [lower_bound, upper_bound]
    // (incusive). Biased towards values around the bounds:
    // lower_bound, lower_bound + 1, upper_bound, upper_bound - 1.
    template <Traits traits>
    uint256_t StakingContractMachine<traits>::gen_bound_biased_uint256(
        uint256_t lower_bound, uint256_t upper_bound)
    {
        MONAD_ASSERT(lower_bound <= upper_bound);
        return discrete_choice<uint256_t>(
            engine_,
            [&, this](auto &) {
                auto const x = gen_uint256();
                auto const m = upper_bound - lower_bound + 1;
                return m ? lower_bound + x % m : x;
            },
            Choice(
                0.05,
                [&](auto &) {
                    return lower_bound == upper_bound ? lower_bound
                                                      : lower_bound + 1;
                }),
            Choice(
                0.05,
                [&](auto &) {
                    return lower_bound == upper_bound ? upper_bound
                                                      : upper_bound - 1;
                }),
            Choice(0.05, [&](auto &) { return lower_bound; }),
            Choice(0.05, [&](auto &) { return upper_bound; }));
    }

    // Generate a random uint256 in the range [lower_bound, upper_bound]
    // (incusive). Biased around values that have been verified to increase
    // code path coverage.
    template <Traits traits>
    uint256_t StakingContractMachine<traits>::gen_stake(
        uint256_t lower_bound, uint256_t upper_bound)
    {
        MONAD_ASSERT(upper_bound >= lower_bound);
        auto optional_result = [&](uint256_t const &stake) {
            bool const inside = stake >= lower_bound && stake <= upper_bound;
            if (upper_bound - lower_bound < stake) {
                if (inside) {
                    return std::optional<uint256_t>{stake};
                }
                return std::optional<uint256_t>{};
            }
            if (inside) {
                return discrete_choice<std::optional<uint256_t>>(
                    engine_,
                    [&](auto &) -> std::optional<uint256_t> {
                        return lower_bound + stake;
                    },
                    Choice(
                        0.33,
                        [&](auto &) -> std::optional<uint256_t> {
                            return upper_bound - stake;
                        }),
                    Choice(0.33, [&](auto &) -> std::optional<uint256_t> {
                        return stake;
                    }));
            }
            else {
                return discrete_choice<std::optional<uint256_t>>(
                    engine_,
                    [&](auto &) -> std::optional<uint256_t> {
                        return lower_bound + stake;
                    },
                    Choice(0.50, [&](auto &) -> std::optional<uint256_t> {
                        return upper_bound - stake;
                    }));
            }
        };

        auto const early_result = discrete_choice<std::optional<uint256_t>>(
            engine_,
            [&](auto &) { return std::optional<uint256_t>{}; },
            Choice(
                0.10,
                [&](auto &) { return optional_result(DUST_THRESHOLD - 1); }),
            Choice(
                0.10, [&](auto &) { return optional_result(DUST_THRESHOLD); }),
            Choice(
                0.10,
                [&](auto &) { return optional_result(DUST_THRESHOLD + 1); }),
            Choice(
                0.10,
                [&](auto &) {
                    return optional_result(MIN_VALIDATE_STAKE - 1);
                }),
            Choice(
                0.10,
                [&](auto &) { return optional_result(MIN_VALIDATE_STAKE); }),
            Choice(
                0.10,
                [&](auto &) {
                    return optional_result(MIN_VALIDATE_STAKE + 1);
                }),
            Choice(
                0.10,
                [&](auto &) {
                    return optional_result(ACTIVE_VALIDATOR_STAKE - 1);
                }),
            Choice(
                0.10,
                [&](auto &) {
                    return optional_result(ACTIVE_VALIDATOR_STAKE);
                }),
            Choice(0.10, [&](auto &) {
                return optional_result(ACTIVE_VALIDATOR_STAKE + 1);
            }));
        if (early_result.has_value()) {
            return *early_result;
        }
        return gen_bound_biased_uint256(lower_bound, upper_bound);
    }

    template <Traits traits>
    Address
    StakingContractMachine<traits>::gen_delegator_to_val_id(u64_be val_id)
    {
        MONAD_ASSERT(model_.val_execution(val_id).exists());
        auto ds = model_.get_delegators_for_validator(val_id);
        MONAD_ASSERT(!ds.empty());
        return ds[gen() % ds.size()];
    }

    template <Traits traits>
    std::optional<u64_be>
    StakingContractMachine<traits>::gen_active_consensus_val_id()
    {
        auto const valset = model_.in_epoch_delay_period()
                                ? model_.valset_snapshot()
                                : model_.valset_consensus();
        auto const n = valset.length();
        if (n == 0) {
            return std::nullopt;
        }
        return valset.get(gen() % n).load().native();
    }

    template <Traits traits>
    void StakingContractMachine<traits>::syscall_on_epoch_change()
    {
        uint64_t next_epoch{};
        if (model_.epoch() == 0) {
            next_epoch = 1 + gen() % 1'000'000;
            auto const res = model_.syscall_on_epoch_change(next_epoch);
            MONAD_ASSERT(res.has_value());
        }
        else {
            next_epoch = model_.epoch() + 1;
            if (!model_.in_epoch_delay_period()) {
                auto const res = model_.syscall_snapshot();
                MONAD_ASSERT(res.has_value());
            }
            auto const res = model_.syscall_on_epoch_change(next_epoch);
            MONAD_ASSERT(res.has_value());
        }

        // Post conditions:

        MONAD_ASSERT(!model_.in_epoch_delay_period());

        MONAD_ASSERT(model_.epoch() == next_epoch);

        for_all_val_ids([&](u64_be v) {
            MONAD_ASSERT(
                model_.active_consensus_stake(v) ==
                model_.consensus_view(v).stake().load().native());
        });
    }

    template <Traits traits>
    void StakingContractMachine<traits>::syscall_snapshot()
    {
        if (model_.epoch() == 0) {
            return;
        }
        if (model_.in_epoch_delay_period()) {
            auto const res = model_.syscall_on_epoch_change(model_.epoch() + 1);
            MONAD_ASSERT(res.has_value());
        }
        auto const res = model_.syscall_snapshot();
        MONAD_ASSERT(res.has_value());

        // Post conditions:

        MONAD_ASSERT(model_.in_epoch_delay_period());

        auto const valset_execution = model_.valset_execution();
        auto const valset_execution_length = valset_execution.length();
        for (uint64_t i = 0; i < valset_execution_length; ++i) {
            auto const v = valset_execution.get(i).load().native();
            MONAD_ASSERT(
                model_.val_execution(v).stake().load().native() >=
                ACTIVE_VALIDATOR_STAKE);
        }

        std::unordered_set<uint64_t> valset_consensus;
        auto model_valset_consensus = model_.valset_consensus();
        auto const valset_consensus_length = model_valset_consensus.length();
        for (uint64_t i = 0; i < valset_consensus_length; ++i) {
            auto const v = model_valset_consensus.get(i).load().native();
            valset_consensus.insert(v);
        }

        for_all_val_ids([&, this](u64_be v) {
            for_all_val_ids([&, this](u64_be u) {
                if (valset_consensus.contains(v.native()) &&
                    !valset_consensus.contains(u.native())) {
                    bool const is_stake_larger =
                        model_.val_execution(v).stake().load().native() >=
                        model_.val_execution(u).stake().load().native();
                    auto const ua = model_.val_execution(u).auth_address();
                    auto const ua_stake =
                        model_.delegator(u, ua).stake().load().native() +
                        model_.delegator(u, ua).delta_stake().load().native() +
                        model_.delegator(u, ua)
                            .next_delta_stake()
                            .load()
                            .native();
                    MONAD_ASSERT(
                        is_stake_larger || ua_stake < MIN_VALIDATE_STAKE);
                }
            });
        });
    }

    template <Traits traits>
    void StakingContractMachine<traits>::syscall_reward()
    {
        auto const pre_val_id = gen_active_consensus_val_id();
        if (!pre_val_id.has_value()) {
            return;
        }
        auto const val_id = *pre_val_id;
        auto const signer = val_id_to_signer_.at(val_id.native());
        auto const reward = gen_bound_biased_uint256(0, 1'000'000 * MON);

        auto const error_bound_before = model_.error_bound();

        std::vector<uint256_t> unit_bias_rewards_before;
        for_all_addresses([&, this](Address const &a) {
            unit_bias_rewards_before.push_back(
                model_.unit_bias_rewards(val_id, a));
        });

        auto const unclaimed_rewards_before =
            model_.val_execution(val_id).unclaimed_rewards().load().native();

        auto const res = model_.syscall_reward<traits>(signer, reward);
        MONAD_ASSERT(res.has_value());

        // Post conditions:

        MONAD_ASSERT(model_.error_bound() == error_bound_before + 1);

        auto const auth_address = model_.val_execution(val_id).auth_address();
        auto const commission =
            (reward * model_.active_consensus_commission(val_id)) / MON;
        auto const rpt = ((reward - commission) * UNIT_BIAS) /
                         model_.active_consensus_stake(val_id);

        {
            size_t i = 0;
            for_all_addresses([&, this](Address const &a) {
                auto const before = unit_bias_rewards_before.at(i++);
                auto const after = model_.unit_bias_rewards(val_id, a);
                auto const epoch = model_.epoch();
                auto const d = model_.delegator_stake(val_id, a, epoch) +
                               model_.withdrawal_stake(val_id, a, epoch);
                auto const r = d * rpt;
                if (a == auth_address) {
                    MONAD_ASSERT(after == before + r + commission * UNIT_BIAS);
                }
                else {
                    MONAD_ASSERT(after == before + r);
                }
            });
        }

        MONAD_ASSERT(
            model_.val_execution(val_id).unclaimed_rewards().load().native() ==
            unclaimed_rewards_before + reward - commission);
    }

    template <Traits traits>
    Address
    StakingContractMachine<traits>::get_add_validator_message_auth_address(
        byte_string const &msg)
    {
        Address a;
        std::memcpy(a.bytes, &msg[81], sizeof(a.bytes));
        return a;
    }

    template <Traits traits>
    std::tuple<
        Address, byte_string, byte_string, byte_string, Address, evmc_uint256be>
    StakingContractMachine<traits>::gen_precompile_add_validator_input(
        uint256_t const &min_stake, uint256_t const &max_stake)
    {
        MONAD_ASSERT(min_stake >= MIN_VALIDATE_STAKE);
        MONAD_ASSERT(max_stake >= min_stake);
        MONAD_ASSERT(max_stake <= MAX_STAKE);

        Address const sender = gen_new_or_old_address();
        uint256_t const stake = gen_stake(min_stake, max_stake);
        auto const value = intx::be::store<evmc_uint256be>(stake);
        Address const auth_address = gen_new_or_old_address();
        auto const commission = gen_bound_biased_uint256(0, MAX_COMMISSION);
        auto const secret = intx::be::store<evmc::bytes32>(gen_uint256());

        auto [msg, secp, bls, signer] = craft_add_validator_input_raw(
            auth_address, stake, commission, secret);

        return {signer, msg, secp, bls, sender, value};
    }

    template <Traits traits>
    u64_be StakingContractMachine<traits>::model_precompile_add_validator(
        Address const &signer, byte_string const &msg, byte_string const &secp,
        byte_string const &bls, Address const &sender,
        evmc_uint256be const &value)
    {
        auto result = model_.precompile_add_validator<traits>(
            msg, secp, bls, sender, value);
        MONAD_ASSERT(result.has_value());

        auto const val_id = result.value();

        all_val_ids_.push_back(val_id);
        if (intx::be::load<uint256_t>(value.bytes) <= MAX_DELEGABLE_STAKE) {
            MONAD_ASSERT(model_.val_execution(val_id).exists());
            auto const ins = delegable_val_ids_.insert(val_id.native());
            MONAD_ASSERT(ins);
        }

        auto const auth_address = get_add_validator_message_auth_address(msg);

        auto ins1 = all_delegators_.insert({val_id.native(), auth_address});
        MONAD_ASSERT(ins1);

        auto [_, ins2] = val_id_to_signer_.insert({val_id.native(), signer});
        MONAD_ASSERT(ins2);

        validator_auth_addresses_.emplace_back(val_id, auth_address);

        return val_id;
    }

    template <Traits traits>
    void StakingContractMachine<traits>::precompile_add_validator()
    {
        auto const [signer, msg, secp, bls, sender, value] =
            gen_precompile_add_validator_input(MIN_VALIDATE_STAKE, MAX_STAKE);

        auto const balance_before = model_.balance_of(STAKING_CA);
        auto const last_val_id_before = model_.last_val_id();

        auto const v = model_precompile_add_validator(
            signer, msg, secp, bls, sender, value);

        auto const balance_after = model_.balance_of(STAKING_CA);

        auto const stake = intx::be::load<uint256_t>(value);

        MONAD_ASSERT(balance_after - balance_before == stake);

        auto const last_val_id_after = model_.last_val_id();

        MONAD_ASSERT(last_val_id_after == last_val_id_before + 1);

        byte_string_view reader{msg};
        auto const secp_pubkey_compressed =
            unaligned_load<byte_string_fixed<33>>(
                consume_bytes(reader, 33).data());
        auto const bls_pubkey_compressed =
            unaligned_load<byte_string_fixed<48>>(
                consume_bytes(reader, 48).data());
        auto const auth_address = unaligned_load<Address>(
            consume_bytes(reader, sizeof(Address)).data());
        auto const signed_stake = unaligned_load<evmc_uint256be>(
            consume_bytes(reader, sizeof(evmc_uint256be)).data());
        auto const commission = unaligned_load<u256_be>(
            consume_bytes(reader, sizeof(u256_be)).data());

        (void)signed_stake;

        auto keys = model_.val_execution(v).keys().load();
        MONAD_ASSERT(keys.secp_pubkey == secp_pubkey_compressed);
        MONAD_ASSERT(keys.bls_pubkey == bls_pubkey_compressed);

        MONAD_ASSERT(
            model_.val_execution(v).commission().load().native() == commission);

        MONAD_ASSERT(model_.val_execution(v).stake().load().native() == stake);

        auto const new_stake_epoch = [this] {
            if (model_.in_epoch_delay_period()) {
                return model_.epoch() + 2;
            }
            else {
                return model_.epoch() + 1;
            }
        }();
        for (auto e = new_stake_epoch; e < model_.epoch() + 5; ++e) {
            MONAD_ASSERT(model_.delegator_stake(v, auth_address, e) == stake);
        }

        auto const valset_execution = model_.valset_execution();
        auto const valset_execution_length = valset_execution.length();
        for (uint64_t i = 0; i < valset_execution_length; ++i) {
            auto const w = valset_execution.get(i).load().native();
            if (v == w) {
                MONAD_ASSERT(stake >= ACTIVE_VALIDATOR_STAKE);
                break;
            }
        }

        bool found_val = false;
        auto const all_vals = model_.get_validators_for_delegator(auth_address);
        for (auto const w : all_vals) {
            if (v == w) {
                found_val = true;
                break;
            }
        }
        MONAD_ASSERT(found_val);
    }

    template <Traits traits>
    std::tuple<u64_be, Address, evmc_uint256be>
    StakingContractMachine<traits>::gen_precompile_delegate_input()
    {
        auto const &sender = gen_new_or_old_address();
        using R = std::tuple<u64_be, Address, evmc_uint256be>;
        return discrete_choice<R>(
            engine_,
            [&, this](auto &) -> R {
                auto const val_id = gen_delegable_val_id();
                auto const val_stake =
                    model_.val_execution(val_id).stake().load().native();
                MONAD_ASSERT(val_stake <= MAX_DELEGABLE_STAKE);
                auto const del_stake =
                    gen_stake(MIN_DELEGATE_STAKE, MAX_STAKE - val_stake);
                auto const value = intx::be::store<evmc_uint256be>(del_stake);
                return {val_id, sender, value};
            },
            Choice(0.01, [&, this](auto &) -> R {
                return {gen_potential_val_id(), sender, evmc_uint256be{}};
            }));
    }

    template <Traits traits>
    void StakingContractMachine<traits>::model_precompile_delegate(
        u64_be val_id, Address const &sender, evmc_uint256be const &value)
    {
        auto result = model_.precompile_delegate<traits>(val_id, sender, value);
        MONAD_ASSERT(result.has_value());

        if (intx::be::load<uint256_t>(value) == 0) {
            return;
        }

        auto const val_stake =
            model_.val_execution(val_id).stake().load().native();
        if (val_stake > MAX_DELEGABLE_STAKE) {
            auto const er = delegable_val_ids_.erase(val_id.native());
            MONAD_ASSERT(er);
        }
        all_delegators_.insert({val_id.native(), sender});
    }

    template <Traits traits>
    void StakingContractMachine<traits>::precompile_delegate()
    {
        auto const [val_id, sender, value] = gen_precompile_delegate_input();

        auto const balance_before = model_.balance_of(STAKING_CA);
        auto const new_stake_epoch = [this] {
            if (model_.in_epoch_delay_period()) {
                return model_.epoch() + 2;
            }
            else {
                return model_.epoch() + 1;
            }
        }();
        auto const new_stake_epoch_end = model_.epoch() + 6;

        std::vector<uint256_t> delegator_stakes_before;
        for (auto e = new_stake_epoch; e < new_stake_epoch_end; ++e) {
            delegator_stakes_before.push_back(
                model_.delegator_stake(val_id, sender, e));
        }

        auto const val_stake_before =
            model_.val_execution(val_id).stake().load().native();

        auto const error_bound_before = model_.error_bound();

        model_precompile_delegate(val_id, sender, value);

        auto const balance_after = model_.balance_of(STAKING_CA);

        auto const stake = intx::be::load<uint256_t>(value);

        if (!stake) {
            return;
        }

        MONAD_ASSERT(balance_after - balance_before == stake);

        for (uint64_t e = new_stake_epoch, i = 0; e < new_stake_epoch_end;
             ++e) {
            MONAD_ASSERT(
                model_.delegator_stake(val_id, sender, e) ==
                delegator_stakes_before.at(i++) + stake);
        }

        auto const val_stake_after =
            model_.val_execution(val_id).stake().load().native();
        MONAD_ASSERT(val_stake_after - val_stake_before == stake);

        auto auth_del = model_.delegator(
            val_id, model_.val_execution(val_id).auth_address());
        auto const auth_del_stake = auth_del.stake().load().native() +
                                    auth_del.delta_stake().load().native() +
                                    auth_del.next_delta_stake().load().native();
        if (val_stake_after >= ACTIVE_VALIDATOR_STAKE &&
            auth_del_stake >= MIN_VALIDATE_STAKE) {
            bool found_val = false;
            auto const valset_execution = model_.valset_execution();
            auto const valset_execution_length = valset_execution.length();
            for (uint64_t i = 0; i < valset_execution_length; ++i) {
                auto const w = valset_execution.get(i).load().native();
                if (val_id == w) {
                    found_val = true;
                    break;
                }
            }
            MONAD_ASSERT(found_val);
        }

        bool found_val = false;
        auto const all_vals = model_.get_validators_for_delegator(sender);
        for (auto const w : all_vals) {
            if (val_id == w) {
                found_val = true;
                break;
            }
        }
        MONAD_ASSERT(found_val);

        auto const error_bound_after = model_.error_bound();
        MONAD_ASSERT(error_bound_after == error_bound_before + 3);
    }

    template <Traits traits>
    std::optional<std::tuple<u64_be, u256_be, u8_be, Address, evmc_uint256be>>
    StakingContractMachine<traits>::gen_precompile_undelegate_input(
        uint256_t const &min_undelegate)
    {
        u64_be val_id;
        Address sender;
        uint256_t del_stake;

        for (size_t i = 0; i < 10; ++i) {
            std::tie(val_id, sender) = gen_delegator();
            del_stake =
                model_.delegator(val_id, sender).stake().load().native();
            if (del_stake >= min_undelegate) {
                break;
            }
        }
        if (del_stake < min_undelegate) {
            return std::nullopt;
        }

        std::tuple<uint64_t, Address> key{val_id.native(), sender};
        auto wis = available_withdrawal_ids_.find(key);

        if (wis != available_withdrawal_ids_.end() && wis->second.empty()) {
            auto const [signer, msg, secp, bls, asender, avalue] =
                gen_precompile_add_validator_input(
                    MIN_VALIDATE_STAKE, MAX_DELEGABLE_STAKE);
            val_id = model_precompile_add_validator(
                signer, msg, secp, bls, asender, avalue);
            sender = get_add_validator_message_auth_address(msg);
            wis = available_withdrawal_ids_.end();
            key = {val_id.native(), sender};
            del_stake =
                model_.delegator(val_id, sender).stake().load().native();
        }

        if (wis == available_withdrawal_ids_.end()) {
            std::vector<u8_be> wi;
            wi.reserve(256);
            for (size_t i = 0; i < 256; ++i) {
                wi.emplace_back(static_cast<uint8_t>(i));
            }
            auto const [it, _] =
                available_withdrawal_ids_.insert({key, std::move(wi)});
            wis = it;
        }

        auto &wi = wis->second;
        MONAD_ASSERT(!wi.empty());

        auto const w = wi[gen() % wi.size()];

        auto const undelegate_stake = gen_stake(min_undelegate, del_stake);

        return {{val_id, undelegate_stake, w, sender, evmc_uint256be{}}};
    }

    template <Traits traits>
    void StakingContractMachine<traits>::model_precompile_undelegate(
        u64_be val_id, u256_be stake, u8_be wid, Address const &sender,
        evmc_uint256be const &value)
    {
        MONAD_ASSERT(model_.val_execution(val_id).exists());

        auto result = model_.precompile_undelegate<traits>(
            val_id, stake, wid, sender, value);
        MONAD_ASSERT(result.has_value());

        if (stake.native() == 0) {
            return;
        }

        std::tuple<uint64_t, Address> const key{val_id.native(), sender};
        auto wis = available_withdrawal_ids_.find(key);
        auto const pos = std::find(wis->second.begin(), wis->second.end(), wid);
        MONAD_ASSERT(pos != wis->second.end());
        wis->second.erase(pos);

        auto const ins = all_withdrawal_requests_.insert(
            {val_id.native(), sender, wid.native()});
        MONAD_ASSERT(ins);

        auto const del_stake =
            model_.delegator(val_id, sender).stake().load().native();
        if (del_stake == 0) {
            auto const er = all_delegators_.erase({val_id.native(), sender});
            MONAD_ASSERT(er);
        }
        auto const val_stake =
            model_.val_execution(val_id).stake().load().native();
        if (val_stake <= MAX_DELEGABLE_STAKE) {
            delegable_val_ids_.insert(val_id.native());
        }
    }

    template <Traits traits>
    void StakingContractMachine<traits>::precompile_undelegate()
    {
        auto const input = gen_precompile_undelegate_input(0);
        MONAD_ASSERT(input.has_value());
        auto const [val_id, stake, wid, sender, value] = *input;

        auto del = model_.delegator(val_id, sender);
        uint256_t sigma = del.stake().load().native();
        if (del.get_delta_epoch().native() <= model_.epoch()) {
            sigma += del.delta_stake().load().native();
        }
        if (del.get_next_delta_epoch().native() <= model_.epoch()) {
            sigma += del.next_delta_stake().load().native();
        }

        auto const effective_stake = [&] {
            if (sigma - stake.native() < DUST_THRESHOLD) {
                return sigma;
            }
            else {
                return stake.native();
            }
        }();

        auto const new_stake_epoch = [this] {
            if (model_.in_epoch_delay_period()) {
                return model_.epoch() + 2;
            }
            else {
                return model_.epoch() + 1;
            }
        }();
        auto const new_stake_epoch_end = model_.epoch() + 6;

        std::vector<uint256_t> delegator_stakes_before;
        for (auto e = new_stake_epoch; e < new_stake_epoch_end; ++e) {
            delegator_stakes_before.push_back(
                model_.delegator_stake(val_id, sender, e));
        }

        std::vector<uint256_t> withdrawal_stakes_before;
        for (uint64_t e = model_.epoch(); e < new_stake_epoch; ++e) {
            withdrawal_stakes_before.push_back(
                model_.withdrawal_stake(val_id, sender, e));
        }

        auto const error_bound_before = model_.error_bound();

        model_precompile_undelegate(val_id, stake, wid, sender, value);

        if (stake.native() == 0) {
            return;
        }

        auto const withdrawal_request =
            model_.withdrawal_request(val_id, sender, wid).load();

        MONAD_ASSERT(withdrawal_request.amount.native() == effective_stake);

        MONAD_ASSERT(withdrawal_request.epoch.native() == new_stake_epoch);

        for (uint64_t e = model_.epoch(), i = 0; e < new_stake_epoch; ++e) {
            MONAD_ASSERT(
                model_.withdrawal_stake(val_id, sender, e) ==
                withdrawal_stakes_before.at(i++) + effective_stake);
        }

        for (uint64_t e = new_stake_epoch, i = 0; e < new_stake_epoch_end;
             ++e) {
            MONAD_ASSERT(
                model_.delegator_stake(val_id, sender, e) ==
                delegator_stakes_before.at(i++) - effective_stake);
        }

        if (sigma == 0) {
            bool found_val = false;
            auto const all_vals = model_.get_validators_for_delegator(sender);
            for (auto const w : all_vals) {
                if (val_id == w) {
                    found_val = true;
                    break;
                }
            }
            MONAD_ASSERT(!found_val);
        }

        auto const error_bound_after = model_.error_bound();
        MONAD_ASSERT(error_bound_after == error_bound_before + 3);
    }

    template <Traits traits>
    std::optional<std::tuple<u64_be, Address, evmc_uint256be>>
    StakingContractMachine<traits>::gen_precompile_compound_input()
    {
        u64_be val_id = 0;
        Address sender;
        uint256_t rewards;
        with_probability(engine_, 0.005, [&](auto &) {
            // Small probability of arbitrary val_id and sender
            val_id = gen() % (model_.last_val_id() + 3);
            sender = gen_new_or_old_address();
            rewards =
                model_.delegator(val_id, sender).rewards().load().native() +
                model_.unaccumulated_rewards(val_id, sender);
        });
        if (sender != Address{}) {
            auto const val_stake =
                model_.val_execution(val_id).stake().load().native();
            if (val_stake + rewards <= MAX_STAKE &&
                (rewards == 0 || rewards >= MIN_DELEGATE_STAKE)) {
                return {{val_id, sender, evmc_uint256be{}}};
            }
        }
        // Try a few times to find a suitable delegator
        for (size_t iters = 0; iters < 10; ++iters) {
            std::tie(val_id, sender) = gen_delegator();
            rewards =
                model_.delegator(val_id, sender).rewards().load().native() +
                model_.unaccumulated_rewards(val_id, sender);
            if (rewards == 0) {
                return {{val_id, sender, evmc_uint256be{}}};
            }
            if (rewards >= MIN_DELEGATE_STAKE) {
                auto const val_stake =
                    model_.val_execution(val_id).stake().load().native();
                if (val_stake + rewards <= MAX_STAKE) {
                    return {{val_id, sender, evmc_uint256be{}}};
                }
            }
        }
        return std::nullopt;
    }

    template <Traits traits>
    void StakingContractMachine<traits>::model_precompile_compound(
        u64_be val_id, Address const &sender, evmc_uint256be const &value)
    {
        uint256_t const rewards =
            model_.delegator(val_id, sender).rewards().load().native() +
            model_.unaccumulated_rewards(val_id, sender);

        auto const res =
            model_.precompile_compound<traits>(val_id, sender, value);
        MONAD_ASSERT(res.has_value());

        if (rewards == 0) {
            return;
        }

        auto const val_stake =
            model_.val_execution(val_id).stake().load().native();
        MONAD_ASSERT(val_stake <= MAX_STAKE);
        if (val_stake > MAX_DELEGABLE_STAKE) {
            auto const er = delegable_val_ids_.erase(val_id.native());
            MONAD_ASSERT(er);
        }
    }

    template <Traits traits>
    bool StakingContractMachine<traits>::precompile_compound()
    {
        auto const input = gen_precompile_compound_input();
        if (!input.has_value()) {
            return false;
        }
        auto const [val_id, sender, value] = *input;

        uint256_t const rewards =
            model_.delegator(val_id, sender).rewards().load().native() +
            model_.unaccumulated_rewards(val_id, sender);

        auto const new_stake_epoch = [this] {
            if (model_.in_epoch_delay_period()) {
                return model_.epoch() + 2;
            }
            else {
                return model_.epoch() + 1;
            }
        }();
        auto const new_stake_epoch_end = model_.epoch() + 6;

        std::vector<uint256_t> delegator_stakes_before;
        for (auto e = new_stake_epoch; e < new_stake_epoch_end; ++e) {
            delegator_stakes_before.push_back(
                model_.delegator_stake(val_id, sender, e));
        }

        auto const val_stake_before =
            model_.val_execution(val_id).stake().load().native();

        auto const unit_bias_rewards_before =
            model_.unit_bias_rewards(val_id, sender);

        auto const error_bound_before = model_.error_bound();

        model_precompile_compound(val_id, sender, value);

        if (rewards == 0) {
            return true;
        }

        for (uint64_t e = new_stake_epoch, i = 0; e < new_stake_epoch_end;
             ++e) {
            MONAD_ASSERT(
                model_.delegator_stake(val_id, sender, e) ==
                delegator_stakes_before.at(i++) + rewards);
        }

        auto const val_stake_after =
            model_.val_execution(val_id).stake().load().native();
        MONAD_ASSERT(val_stake_after - val_stake_before == rewards);

        auto auth_del = model_.delegator(
            val_id, model_.val_execution(val_id).auth_address());
        auto const auth_del_stake = auth_del.stake().load().native() +
                                    auth_del.delta_stake().load().native() +
                                    auth_del.next_delta_stake().load().native();
        if (val_stake_after >= ACTIVE_VALIDATOR_STAKE &&
            auth_del_stake >= MIN_VALIDATE_STAKE) {
            bool found_val = false;
            auto const valset_execution = model_.valset_execution();
            auto const valset_execution_length = valset_execution.length();
            for (uint64_t i = 0; i < valset_execution_length; ++i) {
                auto const w = valset_execution.get(i).load().native();
                if (val_id == w) {
                    found_val = true;
                    break;
                }
            }
            MONAD_ASSERT(found_val);
        }

        auto const error_bound_after = model_.error_bound();
        MONAD_ASSERT(error_bound_after == error_bound_before + 3);

        auto const unit_bias_rewards_after =
            model_.unit_bias_rewards(val_id, sender);
        MONAD_ASSERT(
            unit_bias_rewards_after ==
            unit_bias_rewards_before - rewards * UNIT_BIAS);

        return true;
    }

    template <Traits traits>
    std::optional<std::tuple<u64_be, u8_be, Address, evmc_uint256be>>
    StakingContractMachine<traits>::gen_precompile_withdraw_input()
    {
        if (all_withdrawal_requests_.empty()) {
            auto const input = gen_precompile_undelegate_input(1);
            if (!input.has_value()) {
                return std::nullopt;
            }
            auto const [val_id, stake, wid, sender, value] = *input;
            model_precompile_undelegate(val_id, stake, wid, sender, value);
            MONAD_ASSERT(!all_withdrawal_requests_.empty());
        }
        auto const [pre_val_id, sender, pre_wid] =
            all_withdrawal_requests_.sample(engine_);
        u64_be const val_id = pre_val_id;
        u8_be const wid = pre_wid;

        auto const wit = model_.withdrawal_request(val_id, sender, wid).load();
        auto const wepoch = wit.epoch.native() + WITHDRAWAL_DELAY;
        auto const epoch = model_.epoch();
        if (epoch < wepoch) {
            skip_epochs(wepoch - epoch);
        }
        return {{val_id, wid, sender, evmc_uint256be{}}};
    }

    template <Traits traits>
    void StakingContractMachine<traits>::model_precompile_withdraw(
        u64_be val_id, u8_be wid, Address const &sender,
        evmc_uint256be const &value)
    {
        auto result =
            model_.precompile_withdraw<traits>(val_id, wid, sender, value);
        MONAD_ASSERT(result.has_value());

        std::tuple<uint64_t, Address> const k1{val_id.native(), sender};
        available_withdrawal_ids_.at(k1).push_back(wid);

        auto const er = all_withdrawal_requests_.erase(
            {val_id.native(), sender, wid.native()});
        MONAD_ASSERT(er);
    }

    template <Traits traits>
    bool StakingContractMachine<traits>::precompile_withdraw()
    {
        auto const input = gen_precompile_withdraw_input();
        if (!input.has_value()) {
            return false;
        }
        auto const [val_id, wid, sender, value] = *input;

        auto const staking_balance_before = model_.balance_of(STAKING_CA);
        auto const sender_balance_before = model_.balance_of(sender);
        auto const unclaimed_rewards_before =
            model_.val_execution(val_id).unclaimed_rewards().load().native();
        auto const error_bound_before = model_.error_bound();
        auto const unit_bias_rewards_before =
            model_.unit_bias_rewards(val_id, sender);

        auto const withdrawal_reward =
            model_.withdrawal_reward(val_id, sender, wid);
        auto const withdrawal_amount =
            withdrawal_reward + model_.withdrawal_request(val_id, sender, wid)
                                    .load()
                                    .amount.native();

        model_precompile_withdraw(val_id, wid, sender, value);

        auto const staking_balance_after = model_.balance_of(STAKING_CA);
        MONAD_ASSERT(
            staking_balance_before - staking_balance_after ==
            withdrawal_amount);

        auto const sender_balance_after = model_.balance_of(sender);
        MONAD_ASSERT(
            sender_balance_after - sender_balance_before == withdrawal_amount);

        auto const unclaimed_rewards_after =
            model_.val_execution(val_id).unclaimed_rewards().load().native();
        MONAD_ASSERT(
            unclaimed_rewards_before - unclaimed_rewards_after ==
            withdrawal_reward);

        auto const error_bound_after = model_.error_bound();
        MONAD_ASSERT(error_bound_after == error_bound_before + 1);

        auto const unit_bias_rewards_after =
            model_.unit_bias_rewards(val_id, sender);
        MONAD_ASSERT(
            unit_bias_rewards_before - unit_bias_rewards_after ==
            withdrawal_reward * UNIT_BIAS);

        return true;
    }

    template <Traits traits>
    std::tuple<u64_be, Address, evmc_uint256be>
    StakingContractMachine<traits>::gen_precompile_claim_rewards_input()
    {
        u64_be val_id = 0;
        Address sender;
        with_probability(engine_, 0.005, [&](auto &) {
            // Small probability of arbitrary val_id and sender
            val_id = gen() % (model_.last_val_id() + 3);
            sender = gen_new_or_old_address();
        });
        if (sender != Address{}) {
            return {val_id, sender, evmc_uint256be{}};
        }
        std::tie(val_id, sender) = gen_delegator();
        return {val_id, sender, evmc_uint256be{}};
    }

    template <Traits traits>
    void StakingContractMachine<traits>::model_precompile_claim_rewards(
        u64_be val_id, Address const &sender, evmc_uint256be const &value)
    {
        auto const res =
            model_.precompile_claim_rewards<traits>(val_id, sender, value);
        MONAD_ASSERT(res.has_value());
    }

    template <Traits traits>
    void StakingContractMachine<traits>::precompile_claim_rewards()
    {
        auto const [val_id, sender, value] =
            gen_precompile_claim_rewards_input();

        auto const staking_balance_before = model_.balance_of(STAKING_CA);
        auto const sender_balance_before = model_.balance_of(sender);
        auto const error_bound_before = model_.error_bound();
        auto const unit_bias_rewards_before =
            model_.unit_bias_rewards(val_id, sender);

        auto const reward =
            model_.delegator(val_id, sender).rewards().load().native() +
            model_.unaccumulated_rewards(val_id, sender);

        model_precompile_claim_rewards(val_id, sender, value);

        auto const staking_balance_after = model_.balance_of(STAKING_CA);
        MONAD_ASSERT(staking_balance_before - staking_balance_after == reward);

        auto const sender_balance_after = model_.balance_of(sender);
        MONAD_ASSERT(sender_balance_after - sender_balance_before == reward);

        auto const error_bound_after = model_.error_bound();
        MONAD_ASSERT(error_bound_after == error_bound_before + 3);

        auto const unit_bias_rewards_after =
            model_.unit_bias_rewards(val_id, sender);
        MONAD_ASSERT(
            unit_bias_rewards_before - unit_bias_rewards_after ==
            reward * UNIT_BIAS);
    }

    template <Traits traits>
    std::tuple<u64_be, u256_be, Address, evmc_uint256be>
    StakingContractMachine<traits>::gen_precompile_change_commission_input()
    {
        auto const [val_id, sender] = gen_validator_auth_address();
        auto const commission = gen_bound_biased_uint256(0, MAX_COMMISSION);
        return {val_id, commission, sender, evmc_uint256be{}};
    }

    template <Traits traits>
    void StakingContractMachine<traits>::model_precompile_change_commission(
        u64_be val_id, u256_be const &commission, Address const &sender,
        evmc_uint256be const &value)
    {
        auto const res = model_.precompile_change_commission<traits>(
            val_id, commission, sender, value);
        MONAD_ASSERT(res.has_value());
    }

    template <Traits traits>
    void StakingContractMachine<traits>::precompile_change_commission()
    {
        auto const [val_id, commission, sender, value] =
            gen_precompile_change_commission_input();
        model_precompile_change_commission(val_id, commission, sender, value);
        MONAD_ASSERT(
            model_.val_execution(val_id).commission().load().native() ==
            commission);
    }

    template <Traits traits>
    std::optional<std::tuple<u64_be, Address, evmc_uint256be>>
    StakingContractMachine<traits>::gen_precompile_external_reward_input()
    {
        if (auto const val_id = gen_active_consensus_val_id()) {
            auto const sender = gen_new_or_old_address();
            auto const reward = gen_bound_biased_uint256(
                MIN_EXTERNAL_REWARD, MAX_EXTERNAL_REWARD);
            auto const value = intx::be::store<evmc_uint256be>(reward);
            return {{*val_id, sender, value}};
        }
        return std::nullopt;
    }

    template <Traits traits>
    void StakingContractMachine<traits>::model_precompile_external_reward(
        u64_be val_id, Address const &sender, evmc_uint256be const &value)
    {
        auto const res =
            model_.precompile_external_reward<traits>(val_id, sender, value);
        MONAD_ASSERT(res.has_value());
    }

    template <Traits traits>
    bool StakingContractMachine<traits>::precompile_external_reward()
    {
        auto const input = gen_precompile_external_reward_input();
        if (!input.has_value()) {
            return false;
        }
        auto const [val_id, sender, value] = *input;

        auto const reward = intx::be::load<uint256_t>(value);

        auto const error_bound_before = model_.error_bound();

        std::vector<uint256_t> unit_bias_rewards_before;
        for_all_addresses([&, this](Address const &a) {
            unit_bias_rewards_before.push_back(
                model_.unit_bias_rewards(val_id, a));
        });

        auto const unclaimed_rewards_before =
            model_.val_execution(val_id).unclaimed_rewards().load().native();

        model_precompile_external_reward(val_id, sender, value);

        MONAD_ASSERT(model_.error_bound() == error_bound_before + 1);

        auto const rpt =
            (reward * UNIT_BIAS) / model_.active_consensus_stake(val_id);

        {
            size_t i = 0;
            for_all_addresses([&, this](Address const &a) {
                auto const before = unit_bias_rewards_before.at(i++);
                auto const after = model_.unit_bias_rewards(val_id, a);
                auto const epoch = model_.epoch();
                auto const d = model_.delegator_stake(val_id, a, epoch) +
                               model_.withdrawal_stake(val_id, a, epoch);
                auto const r = d * rpt;
                MONAD_ASSERT(after == before + r);
            });
        }

        MONAD_ASSERT(
            model_.val_execution(val_id).unclaimed_rewards().load().native() ==
            unclaimed_rewards_before + reward);

        return true;
    }

    template <Traits traits>
    std::tuple<u64_be, Address, Address, evmc_uint256be>
    StakingContractMachine<traits>::gen_precompile_get_delegator_input()
    {
        using R = std::tuple<u64_be, Address, Address, evmc_uint256be>;
        return discrete_choice<R>(
            engine_,
            [&, this](auto &) -> R {
                auto const [val_id, addr] = gen_delegator();
                auto const sender = gen_new_or_old_address();
                return {val_id, addr, sender, evmc_uint256be{}};
            },
            Choice(0.05, [&, this](auto &) -> R {
                auto const val_id = gen() % (model_.last_val_id() + 3);
                auto const addr = gen_new_or_old_address();
                auto const sender = gen_new_or_old_address();
                return {val_id, addr, sender, evmc_uint256be{}};
            }));
    }

    template <Traits traits>
    void StakingContractMachine<traits>::model_precompile_get_delegator(
        u64_be val_id, Address const &addr, Address const &sender,
        evmc_uint256be const &value)
    {
        auto const res = model_.precompile_get_delegator<traits>(
            val_id, addr, sender, value);
        MONAD_ASSERT(res.has_value());
    }

    template <Traits traits>
    void StakingContractMachine<traits>::precompile_get_delegator()
    {
        auto const [val_id, addr, sender, value] =
            gen_precompile_get_delegator_input();

        auto const error_bound_before = model_.error_bound();

        auto const delegator_rewards_before =
            model_.delegator(val_id, addr).rewards().load().native();

        auto const unaccumulated_rewards_before =
            model_.unaccumulated_rewards(val_id, addr);

        model_precompile_get_delegator(val_id, addr, sender, value);

        MONAD_ASSERT(model_.error_bound() == error_bound_before + 3);

        MONAD_ASSERT(
            model_.delegator(val_id, addr).rewards().load().native() ==
            delegator_rewards_before + unaccumulated_rewards_before);

        MONAD_ASSERT(model_.unaccumulated_rewards(val_id, addr) == 0);
    }

    EXPLICIT_MONAD_TRAITS_CLASS(StakingContractMachine)
}
