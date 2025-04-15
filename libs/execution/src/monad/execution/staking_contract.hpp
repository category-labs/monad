#pragma once

#include <monad/config.hpp>
#include <monad/contract/mapping.hpp>
#include <monad/contract/storage_array.hpp>
#include <monad/contract/storage_variable.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/core/result.hpp>
#include <monad/execution/staking/types.hpp>

#include <evmc/evmc.h>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

#include <cstdint>
#include <optional>
#include <string_view>

MONAD_NAMESPACE_BEGIN

class State;
struct ValidatorInfo;

enum class StakingSyscallError
{
    Success = 0,
    InvalidValidatorSecpKey,
    InvalidState,
    RewardValidatorNotInSet,
    CouldNotClearStorage,
};

class StakingContract
{
    State &state_;
    Address const &ca_;

public:
    //////////////////////
    //  Revert Codes   //
    //////////////////////
    enum Status
    {
        SUCCESS = 0,
        METHOD_NOT_SUPPORTED,
        INVALID_INPUT,
        VALIDATOR_EXISTS,
        UNKNOWN_VALIDATOR,
        UNKNOWN_DELEGATOR,
        MINIMUM_STAKE_NOT_MET,
        NOT_ENOUGH_SHARES_TO_WITHDRAW,
        INVALID_SECP_PUBKEY,
        INVALID_BLS_PUBKEY,
        INVALID_SECP_SIGNATURE,
        INVALID_BLS_SIGNATURE,
        SECP_SIGNATURE_VERIFICATION_FAILED,
        BLS_SIGNATURE_VERIFICATION_FAILED,
        STATUS_CODES_LENGTH,
    };

    static std::string_view error_message(Status const res)
    {
        static constexpr std::string_view REVERT_MSG[] = {
            "Success",
            "Method not supported",
            "Input invalid",
            "Validator already exists",
            "Unknown validator",
            "Unknown delegator",
            "Minimum stake not met",
            "Not enough shares to withdraw",
            "Invalid secp256k1 pubkey",
            "Invalid bls pubkey",
            "Invalid secp256k1 signature",
            "Secp256k1 signature verification failed",
            "Bls signature verification failed",
            "Invalid bls signature",
        };
        return REVERT_MSG[res];
    }

    StakingContract(State &, Address const &);

    class Variables
    {
        State &state_;
        Address const &ca_;

    public:
        static std::string_view revert_message(Status);

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

        // mapping (address => uint256_t) validator_id
        // This mapping only exists to ensure the same bls_key cannot be
        // assigned to multiple validator ids.
        StorageVariable<uint256_t>
        validator_id_bls(byte_string_fixed<48> const &bls_pubkey) noexcept
        {
            return StorageVariable<uint256_t>(
                state_,
                ca_,
                mapping(
                    0x9b5d94806d34471e95f7972d795def46_bytes32, bls_pubkey));
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

    ////////////////////
    //  Precompiles  //
    ///////////////////
private:
    // helper used by add_stake() and add_validator()
    Status add_stake(
        uint256_t const &validator_id, uint256_t const &amount,
        Address const &);

    Status precompile_add_validator(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Status precompile_add_stake(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Status precompile_remove_stake(
        byte_string_view, evmc_address const &, evmc_uint256be const &);

public:
    Status precompile_dispatch(evmc_message const &);

    ////////////////////
    //  System Calls  //
    ////////////////////
    Result<void> syscall_reward_validator(Address const &);
    Result<void> syscall_on_epoch_change();
};

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::StakingSyscallError>
    : quick_status_code_from_enum_defaults<monad::StakingSyscallError>
{
    static constexpr auto const domain_name = "Staking System Call Error";
    static constexpr auto const domain_uuid =
        "e8858564-6ac9-4f02-899d-bb872d5227f2";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
