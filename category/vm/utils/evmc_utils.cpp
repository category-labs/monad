#include <category/vm/utils/evmc_utils.hpp>

#include <evmc/evmc.hpp>

#include <cstdint>
#include <format>
#include <sstream>
#include <string>

namespace monad::vm::utils
{
    std::string hex_string(evmc::bytes32 const &x)
    {
        std::ostringstream ss(std::ostringstream::ate);
        for (uint8_t const byte : x.bytes) {
            ss << std::format("{:02x}", static_cast<unsigned>(byte));
        }
        return ss.str();
    }
}
