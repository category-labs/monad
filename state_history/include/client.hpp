#pragma once

#include "account.hpp"
#include "bytes.hpp"

#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>

#include <array>
#include <filesystem>
#include <memory>

namespace monad::state_history
{
    struct Client
    {
        using Address = std::array<uint8_t, sizeof(monad::address_t)>;

        std::filesystem::path const root;
        uint64_t const block_number;
        std::string buf;

        Client(std::filesystem::path root, uint64_t block_number)
            : root(root)
            , block_number(block_number)
        {
        }

        [[nodiscard]] std::unique_ptr<Account> get_account(Address) const
        {
            // TODO
            return std::make_unique<Account>();
        }

        [[nodiscard]] constexpr std::string const &get_code(Address) const
        {
            // TODO
            return buf;
        }

        [[nodiscard]] constexpr Bytes32 get_storage_hash(Address) const
        {
            // TODO
            return {};
        }

        [[nodiscard]] constexpr std::string const &
        get_account_proof(Address) const
        {
            // TODO
            return buf;
        }

        [[nodiscard]] constexpr std::string const &
        get_storage_proof(Address, Bytes32) const
        {
            // TODO
            return buf;
        }
    };

    inline std::unique_ptr<Client>
    make_client_at_block_number(std::string const &root, uint64_t block_number)
    {
        return std::make_unique<Client>(root, block_number);
    }

    inline std::unique_ptr<Client> make_client(std::string const &root)
    {
        // TODO:
        return make_client_at_block_number(root, 0);
    }
}
