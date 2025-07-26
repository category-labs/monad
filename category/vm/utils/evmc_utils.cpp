#include <category/vm/utils/evmc_utils.hpp>

#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

#include <cstdint>
#include <format>
#include <sstream>
#include <string>

namespace monad::vm::utils
{
    std::string hex_string(evmc::bytes32 const &x)
    {
        return evmc::hex({x.bytes, sizeof(x.bytes)});
    }

    std::string hex_string(evmc::address const &x)
    {
        return evmc::hex({x.bytes, sizeof(x.bytes)});
    }
}
