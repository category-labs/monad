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

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_tracer_config
{
    NOOP_TRACER = 0,
    CALL_TRACER = 1,
    PRESTATE_TRACER = 2,
    ACCESS_LIST_TRACER = 4,
};

// Options for geth's prestateTracer. A zeroed struct gives geth's defaults,
// and tracers other than PRESTATE_TRACER ignore it.
struct monad_prestate_tracer_config
{
    bool diff_mode;
    // geth's disableCode: accounts with code report codeHash but not code.
    bool disable_code;
};

#ifdef __cplusplus
}
#endif
