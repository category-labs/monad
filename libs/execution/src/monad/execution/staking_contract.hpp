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
        StorageVariable<Uint256BE> epoch{
            state_,
            ca_,
            0x9e3708c603ac673081e26bb54047f80d5cdafe77528853915ad2a74c55155c0e_bytes32};

        StorageVariable<Uint256BE> last_validator_id{
            state_,
            ca_,
            0xcb5af3efd03d626a8756769ffe0b848d51f4dd9a8a4ea88b7d83db13535be6bd_bytes32};

        StorageVariable<Uint256BE> last_deposit_request_id{
            state_,
            ca_,
            0x59725fc1e48c9d8be01f7e99fd22a7aebdb81ead6f187a3aa7f1ed9c2d5786c9_bytes32};

        StorageVariable<Uint256BE> last_withdrawal_request_id{
            state_,
            ca_,
            0xfc1f685954d77928bb8b43407904dc3510647b966f75e0efe3575b5ef5056e80_bytes32};

        StorageArray<Uint256BE> validator_set{
            state_,
            ca_,
            0x72ae25330cca2b1fbd02fe7c6d1ab3960b26f14196d8d23d5f70da5a02c0a073_bytes32};

        ////////////////
        //  Mappings  //
        ////////////////

        // mapping (address => uint256) validator_id
        StorageVariable<Uint256BE> validator_id(Address const &address) noexcept
        {
            return StorageVariable<Uint256BE>(
                state_,
                ca_,
                mapping(
                    0x1218e92019291fc557f47a4668a1b0e9a8461218bdefa517648e349f42bcb1a3_bytes32,
                    address));
        }

        // mapping (address => uint256) validator_id
        // This mapping only exists to ensure the same bls_key cannot be
        // assigned to multiple validator ids.
        StorageVariable<Uint256BE>
        validator_id_bls(byte_string_fixed<48> const &bls_pubkey) noexcept
        {
            return StorageVariable<Uint256BE>(
                state_,
                ca_,
                mapping(
                    0x158c8819b794f76dcd3f66270b7e24e3e3bcca6f80ff106985d16ea43fafda77_bytes32,
                    bls_pubkey));
        }

        // mapping(uint256 => ValidatorInfo) validator_info
        StorageVariable<ValidatorInfo>
        validator_info(Uint256BE const &id) noexcept
        {
            return StorageVariable<ValidatorInfo>(
                state_,
                ca_,
                mapping(
                    0x815e0d4ab52908ec59c74742a0533220a68f43b791154f0ba3b193f4bd8474fe_bytes32,
                    id));
        }

        // mapping(uint256 => mapping(address => DelegatorInfo)) delegator_info
        StorageVariable<DelegatorInfo> delegator_info(
            Uint256BE const &validator_id,
            Address const &address) const noexcept
        {
            return StorageVariable<DelegatorInfo>{
                state_,
                ca_,
                mapping(
                    0x4245010c3499211ecff43d70a64a69d43205b85f984fca1439887714e8f0857c_bytes32,
                    validator_id,
                    address)};
        }

        // mapping(uint256 => DepositRequest) deposit_request
        StorageVariable<DepositRequest>
        deposit_request(Uint256BE const &deposit_id) const noexcept
        {
            return StorageVariable<DepositRequest>{
                state_,
                ca_,
                mapping(
                    0xad6040bcddfdc4135a29f90043f4d16f58b32de144dc68b689436b2f3c83a9f8_bytes32,
                    deposit_id)};
        }

        // mapping(uint256 => WithdrawalRequest) withdrawal_request
        StorageVariable<WithdrawalRequest>
        withdrawal_request(Uint256BE const &withdrawal_id) const noexcept
        {
            return StorageVariable<WithdrawalRequest>{
                state_,
                ca_,
                mapping(
                    0x310389d7b283e0188edf5a44370f9302f17158d3bee6e3fe8939b11f862f0918_bytes32,
                    withdrawal_id)};
        }

        // mapping(uint256 /* epoch */ => Array[u256]) deposit_queue
        StorageArray<Uint256BE>
        deposit_queue(Uint256BE const &epoch) const noexcept
        {
            return StorageArray<Uint256BE>{
                state_,
                ca_,
                mapping(
                    0xca6c90673d5b5445f10b56983d278ce9580be99dd91290b64d4c4a0cd10512ee_bytes32,
                    epoch)};
        }

        // mapping(uint256 /* epoch */ => Array[u256]) withdrawal_queue
        StorageArray<Uint256BE>
        withdrawal_queue(Uint256BE const &epoch) const noexcept
        {
            return StorageArray<Uint256BE>{
                state_,
                ca_,
                mapping(
                    0x2e9329d8bc51599706422b7b26be828c8aa29f11009e2407b9db7897c8b6a6e7_bytes32,
                    epoch)};
        }
    } vars;

    ////////////////////
    //  Precompiles  //
    ///////////////////
private:
    // helper used by add_stake() and add_validator()
    Status add_stake(
        Uint256BE const &validator_id, Uint256BE const &amount,
        Address const &);

public:
    using PrecompileFunc = Status (StakingContract::*)(
        byte_string_view, evmc_address const &, evmc_bytes32 const &);

    static std::pair<PrecompileFunc, uint64_t>
    precompile_dispatch(byte_string_view &);

    Status precompile_fallback(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Status precompile_add_validator(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Status precompile_add_stake(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Status precompile_remove_stake(
        byte_string_view, evmc_address const &, evmc_uint256be const &);

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
