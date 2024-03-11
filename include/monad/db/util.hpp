#pragma once

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/db/config.hpp>
#include <monad/mpt/nibbles_view_fmt.hpp>

#include <ethash/keccak.hpp>

#include <nlohmann/json.hpp>

#include <cstdlib>
#include <filesystem>

MONAD_DB_NAMESPACE_BEGIN

void write_to_file(
    nlohmann::json const &, std::filesystem::path const &, uint64_t const);

constexpr unsigned char state_nibble = 0;
constexpr unsigned char code_nibble = 1;
auto const state_nibbles = mpt::concat(state_nibble);
auto const code_nibbles = mpt::concat(code_nibble);

template <class T>
    requires std::same_as<T, bytes32_t> || std::same_as<T, Address>
constexpr byte_string to_key(T const &arg)
{
    return byte_string{
        std::bit_cast<bytes32_t>(
            ethash::keccak256(arg.bytes, sizeof(arg.bytes)))
            .bytes,
        sizeof(bytes32_t)};
}

MONAD_DB_NAMESPACE_END
