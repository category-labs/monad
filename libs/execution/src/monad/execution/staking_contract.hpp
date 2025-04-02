#pragma once

#include <monad/config.hpp>
#include <monad/contract/mapping.hpp>
#include <monad/contract/storage_array.hpp>
#include <monad/contract/storage_variable.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/execution/staking/types.hpp>

#include <cstdint>
#include <optional>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

class State;
struct ValidatorInfo;

class StakingContract
{
    State &state_;

public:
    StakingContract(State &, Address const &);

    class Variables
    {
        State &state_;
        Address const &ca_;

    public:
        explicit Variables(State &state, Address const &ca)
            : state_{state}
            , ca_{ca}
        {
        }

        /////////////////////////
        //  Constant Addresses //
        /////////////////////////
        StorageVariable<uint256_t> epoch{
            state_, ca_, 0x900cb4cb1c1d43e391b32859defe395e_bytes32};

        StorageVariable<uint256_t> last_validator_id{
            state_, ca_, 0x41220a16053449faaa3a6d09af41bd3e_bytes32};

        StorageVariable<uint256_t> last_deposit_request_id{
            state_, ca_, 0x9e097777443c4f35945fb3a6db51d76c_bytes32};

        StorageVariable<uint256_t> last_withdrawal_request_id{
            state_, ca_, 0x744d787f2587405db4c57efe0e41b665_bytes32};

        StorageArray<uint256_t> validator_set{
            state_, ca_, 0x5da123f52fc44a169234a9b18ac05821_bytes32};

        ////////////////
        //  Mappings  //
        ////////////////

        // mapping (address => uint256_t) validator_id
        StorageVariable<uint256_t> validator_id(Address const &address) noexcept
        {
            return StorageVariable<uint256_t>(
                state_,
                ca_,
                mapping(0x3a5828ff05e4479fbcdc119cf8328b90_bytes32, address));
        }

        // mapping(uint256 => ValidatorInfo) validator_info
        StorageVariable<ValidatorInfo>
        validator_info(uint256_t const &id) noexcept
        {
            return StorageVariable<ValidatorInfo>(
                state_,
                ca_,
                mapping(0xf4e4e229b1c54e1889efc238b4380067_bytes32, id));
        }

        // mapping(uint256 => mapping(address => DelegatorInfo)) delegator_info
        StorageVariable<DelegatorInfo> delegator_info(
            uint256_t const &validator_id,
            Address const &address) const noexcept
        {
            return StorageVariable<DelegatorInfo>{
                state_,
                ca_,
                mapping(
                    0x218c054367a74863b4ba62b844e3c2c0_bytes32,
                    validator_id,
                    address)};
        }

        // mapping(uint256 => DepositRequest) deposit_request
        StorageVariable<DepositRequest>
        deposit_request(uint256_t const &deposit_id) const noexcept
        {
            return StorageVariable<DepositRequest>{
                state_,
                ca_,
                mapping(
                    0xc33a216d11ae4052ae2ff03f00dbca3a_bytes32, deposit_id)};
        }

        // mapping(uint256 => WithdrawalRequest) withdrawal_request
        StorageVariable<WithdrawalRequest>
        withdrawal_request(uint256_t const &withdrawal_id) const noexcept
        {
            return StorageVariable<WithdrawalRequest>{
                state_,
                ca_,
                mapping(
                    0x911c09f7006c4b8b8bb6bed2e426772d_bytes32, withdrawal_id)};
        }

        // mapping(uint256 /* epoch */ => Array[u256]) deposit_queue
        StorageArray<uint256_t>
        deposit_queue(uint256_t const &epoch) const noexcept
        {
            return StorageArray<uint256_t>{
                state_,
                ca_,
                mapping(0xc33a216d11ae4052ae2ff03f00dbca3a_bytes32, epoch)};
        }

        // mapping(uint256 /* epoch */ => Array[u256]) withdrawal_queue
        StorageArray<uint256_t>
        withdrawal_queue(uint256_t const &epoch) const noexcept
        {
            return StorageArray<uint256_t>{
                state_,
                ca_,
                mapping(0xbdde0ce231c849f1adbb75bc51dfe172_bytes32, epoch)};
        }
    } vars;

    // modify validator set
    evmc_status_code add_validator(evmc_message const &);

    // modify delegator set
    evmc_status_code add_stake(evmc_message const &);
    evmc_status_code remove_stake(evmc_message const &);

    // system calls
    void on_epoch_change();
};

MONAD_NAMESPACE_END
