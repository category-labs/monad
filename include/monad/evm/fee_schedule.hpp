#pragma once

#include <monad/evm/config.hpp>
#include <monad/evm/opcodes.hpp>
#include <monad/evm/revision.hpp>
#include <monad/evm/storage_status.hpp>
#include <monad/evm/words.hpp>

#include <cstdint>

MONAD_EVM_NAMESPACE_BEGIN

// Appendix G

// G_zero
constexpr auto zero_cost = 0;

// G_jumpdest
constexpr auto jumpdest_cost = 1;

// G_base
constexpr auto base_cost = 2;

// G_verylow
constexpr auto very_low_cost = 3;

// G_low
constexpr auto low_cost = 5;

// G_mid
constexpr auto mid_cost = 8;

// G_high
constexpr auto high_cost = 10;

// G_warmaccess
template <Revision rev>
constexpr uint64_t warm_access_cost()
{
    if constexpr (rev < Revision::Istanbul) {
        return 200;
    }
    else if constexpr (rev == Revision::Istanbul) {
        return 800;
    }
    else if constexpr (rev >= Revision::Berlin) {
        return 100;
    }
}

// G_coldaccountaccess
template <Revision rev>
constexpr uint64_t cold_account_access_cost()
{
    if constexpr (rev >= Revision::Berlin) {
        return 2600;
    }
}

// G_coldsload
template <Revision rev>
constexpr uint64_t cold_sload_cost()
{
    if constexpr (rev >= Revision::Berlin) {
        return 2100;
    }
}

// G_sset
constexpr uint64_t sset_cost = 20000;

template <Revision rev>
constexpr uint64_t sreset_cost()
{
    if constexpr (rev < Revision::Berlin) {
        return 5000;
    }
    else if constexpr (rev >= Revision::Berlin) {
        return 5000 - cold_sload_cost<rev>();
    }
}

// R_sclear
template <Revision rev>
constexpr uint64_t sclear_refund()
{
    if constexpr (rev < Revision::London) {
        return 15000;
    }
    else if constexpr (rev >= Revision::London) {
        return 4800;
    }
}

// G_selfdestruct
constexpr auto selfdestruct_cost = 5000;

// G_create
constexpr auto create_cost = 32000;

// G_callvalue
constexpr auto call_value_cost = 9000;

// G_callstipend
constexpr auto call_stipend = 2300;

// G_newaccount
constexpr auto new_account_cost = 25000;

// G_exp
constexpr auto exp_cost = 10;

// G_memory
constexpr auto memory_cost = 3;

// G_logtopic
constexpr auto log_topic_cost = 375;

// G_keccak256
constexpr auto keccak256_cost = 30;

// G_keccak256word
constexpr auto keccak256_cost_per_word = 6;

// G_copy
constexpr auto copy_cost_per_word = 3;

// Helpers

template <Revision rev>
constexpr auto additional_cold_account_access_cost =
    cold_account_access_cost<rev>() - warm_access_cost<rev>();

template <Revision rev>
constexpr auto additional_cold_sload_cost =
    cold_sload_cost<rev>() - warm_access_cost<rev>();

template <Revision rev>
constexpr uint64_t sstore_cost(StorageStatus const status)
{
    if constexpr (rev < Revision::Constantinople) {
        switch (status) {
        case StorageStatus::Added:
        case StorageStatus::DeletedThenAdded:
        case StorageStatus::DeletedThenRestored:
            return sset_cost;
        case StorageStatus::Deleted:
        case StorageStatus::Modified:
        case StorageStatus::Assigned:
        case StorageStatus::ModifiedThenDeleted:
        case StorageStatus::AddedThenDeleted:
        case StorageStatus::ModifiedThenRestored:
            return sreset_cost<rev>();
        }
    }
    else {
        switch (status) {
        case StorageStatus::Assigned:
        case StorageStatus::DeletedThenAdded:
        case StorageStatus::ModifiedThenDeleted:
        case StorageStatus::DeletedThenRestored:
        case StorageStatus::AddedThenDeleted:
        case StorageStatus::ModifiedThenRestored:
            return warm_access_cost<rev>();
        case StorageStatus::Added:
            return sset_cost;
        case StorageStatus::Deleted:
        case StorageStatus::Modified:
            return sreset_cost<rev>();
        }
    }
    MONAD_ASSERT(false);
}

template <Revision rev>
constexpr int64_t sstore_refund(StorageStatus const status)
{
    if constexpr (rev < Revision::Constantinople) {
        switch (status) {
        case StorageStatus::Deleted:
        case StorageStatus::ModifiedThenDeleted:
        case StorageStatus::AddedThenDeleted:
            return sclear_refund<rev>();
        case StorageStatus::Added:
        case StorageStatus::DeletedThenAdded:
        case StorageStatus::DeletedThenRestored:
        case StorageStatus::Modified:
        case StorageStatus::Assigned:
        case StorageStatus::ModifiedThenRestored:
            return 0;
        }
    }
    else {
        static_assert(
            sclear_refund<rev>() <= std::numeric_limits<int64_t>::max());
        static_assert(
            sreset_cost<rev>() <= std::numeric_limits<int64_t>::max());
        static_assert(
            warm_access_cost<rev>() <= std::numeric_limits<int64_t>::max());
        switch (status) {
        case StorageStatus::Assigned:
        case StorageStatus::Added:
        case StorageStatus::Modified:
            return 0;
        case StorageStatus::Deleted:
        case StorageStatus::ModifiedThenDeleted:
            return sclear_refund<rev>();
        case StorageStatus::DeletedThenAdded:
            return -static_cast<int64_t>(sclear_refund<rev>());
        case StorageStatus::DeletedThenRestored:
            return static_cast<int64_t>(
                sreset_cost<rev>() - warm_access_cost<rev>() -
                sclear_refund<rev>());
        case StorageStatus::AddedThenDeleted:
            return sset_cost - warm_access_cost<rev>();
        case StorageStatus::ModifiedThenRestored:
            return sreset_cost<rev>() - warm_access_cost<rev>();
        }
    }
    MONAD_ASSERT(false);
}

constexpr uint64_t copy_cost(size_t const n)
{
    return round_up_bytes_to_words(n) * copy_cost_per_word;
}

// template <Revision rev, Opcode op>
// uint64_t baseline_cost();
//
// template <Opcode op>
// constexpr uint64_t baseline_cost<Revision::Frontier, op>()
//{
//     constexpr auto push0 = std::to_underlying(Opcode::PUSH0);
//     constexpr auto push32 = std::to_underlying(Opcode::PUSH32);
//     constexpr auto dup1 = std::to_underlying(Opcode::DUP1);
//     constexpr auto dup16 = std::to_underlying(Opcode::DUP16);
//     constexpr auto swap1 = std::to_underlying(Opcode::SWAP1);
//     constexpr auto swap16 = std::to_underlying(Opcode::SWAP16);
//     constexpr auto log0 = std::to_underlying(Opcode::LOG0);
//     constexpr auto log4 = std::to_underlying(Opcode::LOG4);
//     constexpr auto op_u = std::to_underlying(op);
//
//     if constexpr (
//         op == Opcode::STOP || op == Opcode::SSTORE || op == Opcode::RETURN ||
//         op == Opcode::INVALID || op == Opcode::SELFDESTRUCT) {
//         return zero_cost;
//     }
//     else if constexpr (
//         op == Opcode::ADD || op == Opcode::SUB || op == Opcode::LT ||
//         op == Opcode::GT || op == Opcode::SLT || op == Opcode::SGT ||
//         op == Opcode::EQ || op == Opcode::IZERO || op == Opcode::AND ||
//         op == Opcode::OR || op == Opcode::XOR || op == Opcode::NOT ||
//         op == Opcode::BYTE || op == Opcode::CALLDATALOAD ||
//         op == Opcode::CALLDATACOPY || op == Opcode::CODECOPY ||
//         op == Opcode::MLOAD || op == Opcode::MSTORE || op == Opcode::MSTORE8
//         || (op_u >= push0 && op_u <= push32) || (op_u >= dup1 && op_u <=
//         dup16) || (op_u >= swap1 && op_u <= swap16)) { return very_low_cost;
//     }
//     else if constexpr (
//         op == Opcode::MUL || op == Opcode::DIV || op == Opcode::SDIV ||
//         op == Opcode::MOD || op == Opcode::SMOD || op == Opcode::SIGNEXTEND)
//         { return low_cost;
//     }
//     else if constexpr (
//         op == Opcode::ADDMOD || op == Opcode::MULMOD || op == Opcode::JUMP) {
//         return mid_cost;
//     }
//     else if constexpr (op == Opcode::JUMPI) {
//         return high_cost;
//     }
//     else if constexpr (op == Opcode::EXP) {
//         return exp_cost;
//     }
//     else if constexpr (op == Opcode::KECCAK256) {
//         return keccak256_cost;
//     }
//     else if constexpr (
//         op == Opcode::ADDRESS || op == Opcdoe::ORIGIN || op == Opcode::CALLER
//         || op == Opcode::CALLVALUE || op == Opcode::CALLDATASIZE || op ==
//         Opcode::CODESIZE || op == Opcode::GASPRICE || op == Opcode::COINBASE
//         || op == Opcode::TIMESTAMP || op == Opcode::NUMBER || op ==
//         Opcode::PREVRANDAO || op == Opcode::GASLIMIT || op == Opcode::POP ||
//         op == Opcode::PC || op == Opcode::MSIZE || op == Opcode::GAS) {
//         return base_cost;
//     }
//     else if constexpr (
//         op == Opcode::BALANCE || op == Opcode::EXTCODESIZE ||
//         op == Opcode::EXTCODECOPY || op == Opcode::BLOCKHASH) {
//         return 20;
//     }
//     else if constexpr (op == Opcode::SLOAD) {
//         return 50;
//     }
//     else if constexpr (op == Opcode::JUMPDEST) {
//         return jumpdest_cost;
//     }
//     else if constexpr (op_u >= log0 && op_u <= log4) {
//         return (op_u - log0 + 1) * log_topic_cost;
//     }
//     else if constexpr (op == Opcode::CREATE) {
//         return create_cost;
//     }
//     else if constexpr (op == Opcode::CALL | op == Opcode::CALLCODE) {
//         return 40;
//     }
//     else {
//         static_assert(false, "unrecognized instruction");
//     }
// }
//
// template <Opcode op>
// constexpr uint64_t baseline_cost<Revision::Homestead, op>()
//{
//     if constexpr (op == Opcode::DELEGATECALL) {
//         // EIP-7
//         return 40;
//     }
//     else {
//         return baseline_cost<Revision::Frontier, op>();
//     }
// }
//
// template <Opcode op>
// constexpr uint64_t baseline_cost<Revision::TangerineWhistle, op>()
//{
//     // EIP-150
//     if constexpr (op == Revision::BALANCE) {
//         return 400;
//     }
//     else if constexpr (
//         op == Revision::EXTCODESIZE || op == Opcode::EXTCODECOPY ||
//         op == Opcode::CALL || op == Opcode::CALLCODE ||
//         op == Opcode::DELEGATECALL) {
//         return 700;
//     }
//     else if constexpr (op == Opcode::SLOAD) {
//         return 200;
//     }
//     else if constexpr (op == Opcode::SELFDESTRUCT) {
//         return selfdestruct_cost;
//     }
//     else {
//         return baseline_cost<Revision::Homestead, op>();
//     }
// }
//
// template <Opcode op>
// constexpr uint64_t baseline_cost<Revision::SpuriousDragon, op>()
//{
//     return baseline_cost<Revision::TangerineWhistle, op>();
// }
//
// template <Opcode op>
// constexpr uint64_t baseline_cost<Revision::Byzantium, op>()
//{
//     if constexpr (op == Opcode::RETURNDATASIZE) {
//         // EIP-211
//         return base_cost;
//     }
//     else if constexpr (op == Opcode::RETURNDATACOPY) {
//         // EIP-211
//         return copy_cost_per_word;
//     }
//     else if constexpr (op == Opcode::STATICCALL) {
//         // EIP-214
//         return 700;
//     }
//     else if constexpr (op == Opcode::REVERT) {
//         // EIP-140
//         return zero_cost;
//     }
//     else {
//         return baseline_cost<Revision::SpuriousDragon, op>();
//     }
// }
//
// template <Opcode op>
// constexpr uint64_t baseline_cost<Revision::Constantinople, op>()
//{
//     if constexpr (op == Opcode::SHL || op == Opcode::SHR || op ==
//     Opcode::SAR) {
//         // EIP-145
//         return very_low_cost;
//     }
//     else if constexpr (op == Opcode::EXTCODEHASH) {
//         // EIP-1052
//         return 400;
//     }
//     else if constexpr (op == Opcode::CREATE2) {
//         // EIP-1014
//         return create_cost;
//     }
//     else {
//         return baseline_cost<Revision::Byzantium, op>();
//     }
// }
//
// template <Opcode op>
// constexpr uint64_t baseline_cost<Revision::Petersburg, op>()
//{
//     return baseline_cost<Revision::Constantinople, op>();
// }
//
// template <Opcode op>
// constexpr uint64_t baseline_cost<Revision::Istanbul, op>()
//{
//     if constexpr (op == Opcode::BALANCE || op == Opcode::EXTCODEHASH) {
//         // EIP-1884
//         return 700;
//     }
//     else if constexpr (op == Opcode::CHAINID) {
//         // EIP-1344
//         return base_cost;
//     }
//     else if constexpr (op == Opcode::SELFBALANCE) {
//         // EIP-1884
//         return 5;
//     }
//     else if constexpr (op == Opcode::SLOAD) {
//         // EIP-1884
//         return 800;
//     }
//     else {
//         return baseline_cost<Revision::Petersburg, op>();
//     }
// }
//
// template <Opcode op>
// constexpr uint64_t baseline_cost<Revision::Berlin, op>()
//{
//     // EIP-2929
//     if constexpr (
//         op == Opcode::EXTCODESIZE || op == Opcode::EXTCODEHASH ||
//         op == Opcode::EXTCODECOPY || op == Opcode::BALANCE ||
//         op == Opcode::CALL || op == Opcode::CALLCODE ||
//         op == Opcode::DELEGATECALL || op == Opcode::STATICCALL ||
//         op == Opcode::SLOAD) {
//         return warm_access_cost<Revision::Berlin>();
//     }
//     else {
//         return baseline_cost<Revision::Istanbul, op>();
//     }
// }
//
// template <Opcode op>
// constexpr uint64_t baseline_cost<Revision::London, op>()
//{
//     // EIP-3198
//     if constexpr (op == Opcode::BASEFEE) {
//         return base_cost;
//     }
//     else {
//         return baseline_cost<Revision::Berlin, op>();
//     }
// }
//
// template <Opcode op>
// constexpr uint64_t baseline_cost<Revision::Paris, op>()
//{
//     return baseline_cost<Revision::London, op>();
// }
//
// template <Opcode op>
// constexpr uint64_t baseline_cost<Revision::Shanghai, op>()
//{
//     if constexpr (op == Opcode::PUSH0) {
//         // EIP-3855
//         return base_cost;
//     }
//     else {
//         return baseline_cost<Revision::Paris, op>();
//     }
// }
//
MONAD_EVM_NAMESPACE_END
