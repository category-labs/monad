#pragma once

#include <monad/config.hpp>
#include <monad/contract/storage_array.hpp>
#include <monad/contract/storage_variable.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>

#include <cstdint>
#include <optional>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

class State;
struct ValidatorInfo;

class StakingContract
{
    State &state_;
    uint64_t const epoch_;
    // uint256 last_validator_id
    StorageVariable<uint256_t> last_validator_id_storage_;
    // uint256 last_stake_delta_id
    StorageVariable<uint256_t> last_stake_delta_id_storage_;
    // Array[uint256] validator_set
    StorageArray<uint256_t> validator_set_storage_;

    uint256_t next_validator_id() noexcept;
    uint256_t next_stake_delta_id() noexcept;

    // mapping(address => uint256) validator_id
    void create_validator_id_mapping(
        Secp256k1_Pubkey const &, uint256_t const &) noexcept;

    // mapping(uint256 => ValidatorInfo) validator_info
    void
    add_validator_to_set(uint256_t const &, ValidatorInfo const &) noexcept;

public:
    StakingContract(State &, uint64_t epoch);

    // public getters
    StorageVariable<uint256_t> get_validator_id(Address const &) const noexcept;
    StorageVariable<ValidatorInfo>
    get_validator_info(uint256_t const &) const noexcept;

    // modify validator set
    evmc_status_code
    add_validator(byte_string_view input, evmc_message const &);

    // modify delegator set
    evmc_status_code add_stake(byte_string_view input, evmc_message const &);
    evmc_status_code remove_stake(byte_string_view input, evmc_message const &);
};

MONAD_NAMESPACE_END
