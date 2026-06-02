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

#include <CLI/CLI.hpp>

#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

namespace cli
{
    // CLI11 Formatter that emits clap-style --help output so the Monad
    // execution binaries (monad, monad-cli, monad-mpt) match the help layout
    // produced by the Rust binaries that go through monad-ctl.
    class HelpFormatter : public CLI::Formatter
    {
        std::string version_;
        bool use_color_;

        // Wrap `inner` in an ANSI escape sequence when color is enabled,
        // otherwise return `inner` unchanged.
        std::string
        styled(std::string_view escape, std::string_view inner) const;

    public:
        // `version` is rendered on the first line of --help output ("<bin>
        // <version>").  ANSI bold / underline is enabled when stdout is a
        // TTY and the NO_COLOR environment variable is unset or empty.
        explicit HelpFormatter(std::string version);

        std::string make_help(
            CLI::App const *app, std::string name,
            CLI::AppFormatMode mode) const override;

        std::string make_description(CLI::App const *app) const override;

        std::string
        make_usage(CLI::App const *app, std::string name) const override;

        std::string make_subcommands(
            CLI::App const *app, CLI::AppFormatMode mode) const override;

        std::string
        make_option(CLI::Option const *opt, bool is_positional) const override;

        std::string make_option_name(
            CLI::Option const *opt, bool is_positional) const override;

        std::string make_option_opts(CLI::Option const *opt) const override;

        std::string make_option_desc(CLI::Option const *opt) const override;

        // Configure `app` to use this formatter and install a clap-style
        // help flag ("-h, --help").  Does not install a --version printer
        // (the existing binaries do not expose one today).
        void install(CLI::App &app);
    };
} // namespace cli

MONAD_NAMESPACE_END
