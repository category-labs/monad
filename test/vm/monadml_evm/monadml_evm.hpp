// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

extern "C" struct evmc_vm *evmc_create_monadml_evm() noexcept;
extern "C" struct evmc_vm *evmc_create_monadml_evm_debug_tstore() noexcept;

// The spec VM's release functions are libffi trampolines that can start a page
// with nothing mapped below it; clang's -fsanitize=function reads the 8 bytes
// before an indirect callee, so release here, unchecked, instead of in ~Result.
[[nodiscard, clang::no_sanitize("function")]] inline evmc::Result
copy_monadml_result(evmc::Result spec) noexcept
{
    auto const raw = spec.release_raw();
    evmc::Result result{
        raw.status_code,
        raw.gas_left,
        raw.gas_refund,
        raw.output_data,
        raw.output_size};
    result.create_address = raw.create_address;
    if (raw.release != nullptr) {
        raw.release(&raw);
    }
    return result;
}
