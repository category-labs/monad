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

// Project-internal logging header — the single chokepoint for everything
// the codebase pulls from quill. Files that emit log messages, hold a
// `quill::Logger *`, specialize `quill::copy_loggable`, or use the `fmt::`
// formatter should include this instead of reaching directly into
// `<quill/...>` headers.
//
// Today this re-exports `<quill/Quill.h>`, which transitively provides
// every quill name our code uses (LogLevel, Logger, Handler, FileHandler,
// the bundled `fmtquill` formatter, etc.). The `fmt` alias points at
// `fmtquill` rather than `fmtquill::v10` so it survives the inline-namespace
// tag bump (v10 → v12) in the upcoming quill v11 upgrade — call sites that
// say `fmt::format(...)` keep working without source changes.
//
// The upcoming quill v11 upgrade splits the umbrella across
// Backend/Frontend/LogMacros and removes the QUILL_ROOT_LOGGER_ONLY mode;
// at that point this file becomes where the wrapper macros and
// `quill::get_root_logger()` shim live, so call sites don't need to change
// again.

#include <quill/Quill.h>

namespace fmt = fmtquill;
