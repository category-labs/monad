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

#include <category/core/cli/help_formatter.hpp>

#include <category/core/config.hpp>

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdlib>
#include <format>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include <unistd.h>

MONAD_NAMESPACE_BEGIN

namespace cli
{
    namespace
    {
        // ANSI escape sequences kept short; \x1b[0m fully resets attributes.
        constexpr std::string_view ANSI_BOLD = "\x1b[1m";
        constexpr std::string_view ANSI_BOLD_UNDERLINE = "\x1b[1;4m";
        constexpr std::string_view ANSI_RESET = "\x1b[0m";

        bool detect_color()
        {
            char const *const no_color = std::getenv("NO_COLOR");
            if (no_color != nullptr && no_color[0] != '\0') {
                return false;
            }
            return ::isatty(STDOUT_FILENO) != 0;
        }

        std::string to_placeholder(std::string s)
        {
            for (char &c : s) {
                if (c == '-') {
                    c = '_';
                }
                else {
                    c = static_cast<char>(
                        std::toupper(static_cast<unsigned char>(c)));
                }
            }
            return s;
        }

        bool is_option_group(CLI::App const *const sub)
        {
            return dynamic_cast<CLI::Option_group const *>(sub) != nullptr;
        }

        void collect_options(
            CLI::App const *const app, std::vector<CLI::Option const *> &out,
            bool const is_nested)
        {
            CLI::Option const *const help_ptr = app->get_help_ptr();
            for (auto const *opt :
                 app->get_options([](CLI::Option const *) { return true; })) {
                if (opt->get_group().empty()) {
                    // hidden / internal option
                    continue;
                }
                if (opt->get_positional()) {
                    // positionals are emitted from make_help's Arguments
                    // section so they appear together, separately from flags
                    continue;
                }
                if (is_nested && opt == help_ptr) {
                    // option_groups inherit their own help flag from CLI::App;
                    // surface it once at the top level only
                    continue;
                }
                out.push_back(opt);
            }
            for (auto const *sub :
                 app->get_subcommands([](CLI::App const *) { return true; })) {
                if (is_option_group(sub)) {
                    collect_options(sub, out, /*is_nested=*/true);
                }
            }
        }
    } // namespace

    HelpFormatter::HelpFormatter(std::string version)
        : version_{std::move(version)}
        , use_color_{detect_color()}
    {
    }

    std::string HelpFormatter::styled(
        std::string_view const escape, std::string_view const inner) const
    {
        if (!use_color_) {
            return std::string{inner};
        }
        return std::format("{}{}{}", escape, inner, ANSI_RESET);
    }

    std::string HelpFormatter::make_description(CLI::App const *const app) const
    {
        auto const styled_name = styled(ANSI_BOLD, app->get_name());
        auto const &desc = app->get_description();
        auto const desc_line =
            desc.empty() ? std::string{} : std::format("{}\n", desc);
        return version_.empty()
                   ? std::format("{}\n{}", styled_name, desc_line)
                   : std::format("{} {}\n{}", styled_name, version_, desc_line);
    }

    std::string
    HelpFormatter::make_usage(CLI::App const *const app, std::string name) const
    {
        if (name.empty()) {
            name = app->get_name();
        }

        std::string out = std::format(
            "\n{} {} [OPTIONS]",
            styled(ANSI_BOLD_UNDERLINE, "Usage:"),
            styled(ANSI_BOLD, name));

        auto const real_subs = app->get_subcommands(
            [](CLI::App const *const s) { return !is_option_group(s); });
        if (!real_subs.empty()) {
            out += " [COMMAND]";
        }

        auto const positionals = app->get_options(
            [](CLI::Option const *const o) { return o->get_positional(); });
        if (!positionals.empty()) {
            out += " <ARGS>...";
        }

        out += '\n';
        return out;
    }

    std::string HelpFormatter::make_subcommands(
        CLI::App const *const app, CLI::AppFormatMode /*mode*/) const
    {
        auto const subs = app->get_subcommands(
            [](CLI::App const *const s) { return !is_option_group(s); });
        if (subs.empty()) {
            return {};
        }

        std::size_t max_name = 0;
        for (auto const *sub : subs) {
            max_name = std::max(max_name, sub->get_name().size());
        }

        std::string out =
            std::format("\n{}\n", styled(ANSI_BOLD_UNDERLINE, "Commands:"));
        for (auto const *sub : subs) {
            std::string const &n = sub->get_name();
            out += std::format(
                "  {}{}{}\n",
                styled(ANSI_BOLD, n),
                std::string(max_name - n.size() + 2, ' '),
                sub->get_description());
        }
        return out;
    }

    std::string HelpFormatter::make_help(
        CLI::App const *const app, std::string name,
        CLI::AppFormatMode const mode) const
    {
        if (name.empty()) {
            name = app->get_name();
        }

        auto const render_section = [&](std::string_view const title,
                                        auto const &items,
                                        bool const is_positional) {
            if (items.empty()) {
                return std::string{};
            }
            std::string s =
                std::format("\n{}\n", styled(ANSI_BOLD_UNDERLINE, title));
            for (auto const *opt : items) {
                s += make_option(opt, is_positional);
            }
            return s;
        };

        auto const positionals = app->get_options(
            [](CLI::Option const *const o) { return o->get_positional(); });
        std::vector<CLI::Option const *> opts;
        collect_options(app, opts, /*is_nested=*/false);

        return std::format(
            "{}{}{}{}{}{}",
            make_description(app),
            make_usage(app, name),
            render_section("Arguments:", positionals, /*is_positional=*/true),
            render_section("Options:", opts, /*is_positional=*/false),
            make_subcommands(app, mode),
            make_footer(app));
    }

    std::string HelpFormatter::make_option_name(
        CLI::Option const *const opt, bool const is_positional) const
    {
        if (is_positional) {
            return std::format(
                "  <{}>", to_placeholder(opt->get_name(true, false)));
        }

        auto const &snames = opt->get_snames();
        auto const &lnames = opt->get_lnames();

        if (lnames.empty()) {
            // short-only option: render as "  -s"
            return snames.empty() ? std::string{"  "}
                                  : std::format("  -{}", snames.front());
        }

        // Show only the first long name — CLI11 lets binaries register
        // snake_case aliases (e.g. "--block-db,--block_db") which would
        // otherwise clutter the help output.  Long-only options pad past
        // the "-x, " slot reserved for a short flag.
        return snames.empty()
                   ? std::format("      --{}", lnames.front())
                   : std::format("  -{}, --{}", snames.front(), lnames.front());
    }

    std::string
    HelpFormatter::make_option_opts(CLI::Option const *const opt) const
    {
        if (opt->get_positional()) {
            return {};
        }
        if (opt->get_expected_max() == 0) {
            // flag — consumes no value, no placeholder
            return {};
        }
        // Respect an explicitly-set type_name when the caller wrote a
        // bracketed/structured placeholder (e.g.
        // type_name("<ring-name-or-path>[:<descriptor-shift>:<buf-shift>]")).
        // Bare CLI11 defaults like "TEXT"/"UINT"/"INT" are skipped so we keep
        // the clap-style derived placeholder.
        std::string const &type_name = opt->get_type_name();
        if (!type_name.empty() && type_name.front() == '<') {
            return std::format(" {}", type_name);
        }
        auto const &lnames = opt->get_lnames();
        auto const &snames = opt->get_snames();
        std::string base = !lnames.empty()
                               ? lnames.front()
                               : (!snames.empty() ? snames.front() : "value");
        return std::format(" <{}>", to_placeholder(std::move(base)));
    }

    std::string
    HelpFormatter::make_option_desc(CLI::Option const *const opt) const
    {
        std::string desc = opt->get_description();
        if (opt->get_expected_max() != 0) {
            std::string const def = opt->get_default_str();
            if (!def.empty() && def != "false") {
                if (!desc.empty()) {
                    desc += ' ';
                }
                desc += std::format("[default: {}]", def);
            }
        }
        if (opt->get_required()) {
            if (!desc.empty()) {
                desc += ' ';
            }
            desc += "[required]";
        }
        return desc;
    }

    std::string HelpFormatter::make_option(
        CLI::Option const *const opt, bool const is_positional) const
    {
        std::string const name_plain = make_option_name(opt, is_positional);
        std::string const opts_part = make_option_opts(opt);
        std::string const desc = make_option_desc(opt);

        // Match clap's long-help layout: each option's description appears
        // on the line below the flag, indented to column 10 (4 spaces past
        // the long-only option indent).
        auto const desc_line =
            desc.empty() ? std::string{} : std::format("          {}\n", desc);
        return std::format(
            "{}{}\n{}", styled(ANSI_BOLD, name_plain), opts_part, desc_line);
    }

    void HelpFormatter::install(CLI::App &app)
    {
        app.set_help_flag("-h,--help", "Print help");
        app.formatter(std::make_shared<HelpFormatter>(*this));
    }
} // namespace cli

MONAD_NAMESPACE_END
