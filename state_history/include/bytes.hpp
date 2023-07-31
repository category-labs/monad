#pragma once

#include <monad/core/bytes.hpp>

#include <array>
#include <cstdint>

namespace monad::state_history
{
    using Bytes32 = std::array<uint8_t, sizeof(monad::bytes32_t)>;
}
