// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/monad/core/monad_block.hpp>

#include <filesystem>

MONAD_NAMESPACE_BEGIN

byte_string read_file(bytes32_t const &, std::filesystem::path const &);

MonadConsensusBlockBody
read_body(bytes32_t const &, std::filesystem::path const &);

bytes32_t head_pointer_to_id(std::filesystem::path const &);

MONAD_NAMESPACE_END
