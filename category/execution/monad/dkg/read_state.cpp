// Copyright (C) 2026 Category Labs, Inc.

#include <category/execution/monad/dkg/read_state.hpp>

#include <category/core/int.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/dkg/dkg_contract.hpp>
#include <category/execution/monad/dkg/dkg_error.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/vm.hpp>

#include <boost/outcome/try.hpp>

#include <limits>
#include <utility>

MONAD_NAMESPACE_BEGIN

namespace dkg
{
    namespace
    {
        template <typename F>
        auto read_at_block(mpt::Db &db, size_t const block_num, F &&read)
        {
            vm::VM vm;
            TrieDb trie_db{db};
            trie_db.set_block_and_prefix(block_num);
            BlockState block_state{trie_db, vm};
            Incarnation const incarnation{block_num, Incarnation::LAST_TX - 1u};
            State state{block_state, incarnation};
            NoopCallTracer call_tracer{};

            if (!state.account_exists(staking::STAKING_CA)) {
                using Return = decltype(read(state, call_tracer));
                return Return{DkgError::StakingLookupFailed};
            }
            if (!state.account_exists(DKG_CA)) {
                using Return = decltype(read(state, call_tracer));
                return Return{DkgError::EpochStateUnavailable};
            }
            return read(state, call_tracer);
        }

        void append_uint(byte_string &input, uint64_t const value)
        {
            input += abi_encode_uint(u64_be{value});
        }

        void append_uint(byte_string &input, uint32_t const value)
        {
            input += abi_encode_uint(u32_be{value});
        }

        byte_string page_input(
            uint64_t const epoch, uint64_t const start, uint32_t const limit)
        {
            byte_string input;
            append_uint(input, epoch);
            append_uint(input, start);
            append_uint(input, limit);
            return input;
        }
    }

    Result<RegistrationRead> read_registrations(
        mpt::Db &db, size_t const block_num, uint64_t const epoch,
        std::vector<Address> const &validators)
    {
        return read_at_block(
            db,
            block_num,
            [&](State &state,
                NoopCallTracer &call_tracer) -> Result<RegistrationRead> {
                staking::StakingContract::Variables staking_vars{state};
                uint64_t const staking_epoch =
                    staking_vars.epoch.load().native();
                bool const registration_open =
                    !staking_vars.in_epoch_delay_period.load() &&
                    staking_epoch != std::numeric_limits<uint64_t>::max() &&
                    epoch == staking_epoch + 1;

                DkgContract contract{state, call_tracer, block_num};
                RegistrationRead result{
                    .registration_open = registration_open,
                    .registrations = {}};
                result.registrations.reserve(validators.size());
                for (Address const &validator : validators) {
                    uint64_t const validator_id =
                        staking_vars.val_id(validator).load().native();
                    byte_string input;
                    append_uint(input, epoch);
                    append_uint(input, validator_id);
                    BOOST_OUTCOME_TRY(
                        auto registration,
                        contract.precompile_registration_of(input, {}, {}));
                    result.registrations.push_back(std::move(registration));
                }
                return result;
            });
    }

    Result<byte_string> read_pc_qcs(
        mpt::Db &db, size_t const block_num, uint64_t const epoch,
        uint64_t const start, uint32_t const limit)
    {
        return read_at_block(
            db,
            block_num,
            [&](State &state,
                NoopCallTracer &call_tracer) -> Result<byte_string> {
                DkgContract contract{state, call_tracer, block_num};
                return contract.precompile_pc_qcs(
                    page_input(epoch, start, limit), {}, {});
            });
    }

    Result<byte_string> read_bve_qcs(
        mpt::Db &db, size_t const block_num, uint64_t const epoch,
        uint64_t const start, uint32_t const limit)
    {
        return read_at_block(
            db,
            block_num,
            [&](State &state,
                NoopCallTracer &call_tracer) -> Result<byte_string> {
                DkgContract contract{state, call_tracer, block_num};
                return contract.precompile_bve_qcs(
                    page_input(epoch, start, limit), {}, {});
            });
    }

    Result<byte_string>
    read_dkg_result(mpt::Db &db, size_t const block_num, uint64_t const epoch)
    {
        return read_at_block(
            db,
            block_num,
            [&](State &state,
                NoopCallTracer &call_tracer) -> Result<byte_string> {
                DkgContract contract{state, call_tracer, block_num};
                byte_string input;
                append_uint(input, epoch);
                return contract.precompile_dkg_result(input, {}, {});
            });
    }
}

MONAD_NAMESPACE_END
