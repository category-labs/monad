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

#include <category/core/config.hpp>

#define MONAD_MPT_NAMESPACE_BEGIN                                              \
    MONAD_NAMESPACE_BEGIN namespace mpt                                        \
    {

#define MONAD_MPT_NAMESPACE_END                                                \
    }                                                                          \
    MONAD_NAMESPACE_END

#define MONAD_MPT_NAMESPACE ::monad::mpt

MONAD_MPT_NAMESPACE_BEGIN

static constexpr unsigned EMPTY_STRING_RLP_LENGTH = 1;
static constexpr unsigned char RLP_EMPTY_STRING = 0x80;

MONAD_MPT_NAMESPACE_END