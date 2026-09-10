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

// zkVM shadow of <quill/std/Pair.h>. Quill is dropped from the guest link, so
// the host headers that #include this quill logging-codec support for
// std::pair resolve here instead. Logging is a no-op in the guest (see
// zkvm/category/core/log.hpp), so no codec is needed — intentionally empty.
#pragma once
