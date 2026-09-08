// Copyright (C) 2026 Category Labs, Inc.

#pragma once

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>

#include <cstddef>
#include <cstdint>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace mpt
{
    class Db;
}

namespace dkg
{

    struct RegistrationEntry
    {
        uint64_t validator_id;
        byte_string registration;
    };

    struct RegistrationRead
    {
        bool registration_open;
        std::vector<RegistrationEntry> registrations;
    };

    Result<RegistrationRead> read_registrations(
        mpt::Db &, size_t block_num, uint64_t epoch,
        std::vector<Address> const &validators);

    Result<byte_string> read_pc_qcs(
        mpt::Db &, size_t block_num, uint64_t epoch, uint64_t start,
        uint32_t limit);

    Result<byte_string> read_bve_qcs(
        mpt::Db &, size_t block_num, uint64_t epoch, uint64_t start,
        uint32_t limit);

    Result<byte_string>
    read_dkg_result(mpt::Db &, size_t block_num, uint64_t epoch);

}

MONAD_NAMESPACE_END
