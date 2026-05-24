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
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <CLI/CLI.hpp>

#include <cstddef>
#include <string>

using namespace monad::cli;

namespace
{
    // Strip ANSI CSI escape sequences (\x1b[…m) so the string assertions
    // below stay deterministic regardless of whether the test binary is
    // invoked from a TTY or not.
    std::string strip_ansi(std::string s)
    {
        std::string out;
        out.reserve(s.size());
        for (std::size_t i = 0; i < s.size(); ++i) {
            if (s[i] == '\x1b' && i + 1 < s.size() && s[i + 1] == '[') {
                i += 2;
                while (i < s.size() && s[i] != 'm') {
                    ++i;
                }
                continue;
            }
            out += s[i];
        }
        return out;
    }

    std::string render_help(CLI::App &app)
    {
        return strip_ansi(app.help());
    }
} // namespace

TEST(HelpFormatter, header_has_bin_name_and_version)
{
    CLI::App app{"Test description.", "monad-test"};
    HelpFormatter{"abc123"}.install(app);

    auto const out = render_help(app);
    EXPECT_NE(out.find("monad-test abc123"), std::string::npos)
        << "expected 'monad-test abc123' header in:\n"
        << out;
    EXPECT_NE(out.find("Test description."), std::string::npos);
}

TEST(HelpFormatter, usage_line_uses_clap_style)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);

    auto const out = render_help(app);
    EXPECT_NE(out.find("Usage: monad-test [OPTIONS]"), std::string::npos)
        << out;
}

TEST(HelpFormatter, help_flag_uses_space_separator)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);

    auto const out = render_help(app);
    EXPECT_NE(out.find("-h, --help"), std::string::npos)
        << "expected '-h, --help' (with space) in:\n"
        << out;
    EXPECT_EQ(out.find("-h,--help"), std::string::npos)
        << "must not emit comma-without-space form";
}

TEST(HelpFormatter, options_section_renders_with_value_placeholder)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);
    std::string db;
    app.add_option("--db", db, "database path");

    auto const out = render_help(app);
    EXPECT_NE(out.find("Options:"), std::string::npos) << out;
    EXPECT_NE(out.find("--db <DB>"), std::string::npos)
        << "expected angle-bracketed placeholder '<DB>' in:\n"
        << out;
    EXPECT_NE(out.find("database path"), std::string::npos);
}

TEST(HelpFormatter, description_appears_on_separate_line)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);
    std::string s;
    app.add_option("--db", s, "database path");

    auto const out = render_help(app);
    // Description is on its own line, indented to column 10 (matching clap's
    // long-help layout).
    EXPECT_NE(out.find("--db <DB>\n          database path"), std::string::npos)
        << "expected description on a separate line indented 10 spaces:\n"
        << out;
}

TEST(HelpFormatter, required_suffix_is_appended)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);
    std::string db;
    app.add_option("--db", db, "database path")->required();

    auto const out = render_help(app);
    EXPECT_NE(out.find("[required]"), std::string::npos) << out;
}

TEST(HelpFormatter, default_suffix_renders_for_value_options)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);
    int n = 42;
    app.add_option("--n", n, "an integer")->capture_default_str();

    auto const out = render_help(app);
    EXPECT_NE(out.find("[default: 42]"), std::string::npos) << out;
}

TEST(HelpFormatter, boolean_flag_omits_default_false)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);
    app.option_defaults()->always_capture_default();
    bool verbose = false;
    app.add_flag("--verbose", verbose, "verbose mode");

    auto const out = render_help(app);
    EXPECT_EQ(out.find("[default: false]"), std::string::npos)
        << "boolean flag should not advertise '[default: false]' in:\n"
        << out;
}

TEST(HelpFormatter, long_only_option_is_indented_past_short_slot)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);
    std::string s;
    app.add_option("--only-long", s, "long-only");

    auto const out = render_help(app);
    // Long-only options indent six spaces (2 for the column + 4 to align past
    // the "-x, " slot reserved for a short flag).
    EXPECT_NE(out.find("      --only-long"), std::string::npos)
        << "expected long-only option indented past the short-flag slot in:\n"
        << out;
}

TEST(HelpFormatter, dashes_in_option_names_become_underscores_in_placeholder)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);
    std::string s;
    app.add_option("--log-level", s, "level");

    auto const out = render_help(app);
    EXPECT_NE(out.find("--log-level <LOG_LEVEL>"), std::string::npos) << out;
}

TEST(HelpFormatter, explicit_type_name_is_honored_when_bracketed)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);
    std::string s;
    app.add_option("--ring", s, "event ring config")
        ->type_name("<name>[:<shift>]");

    auto const out = render_help(app);
    EXPECT_NE(out.find("--ring <name>[:<shift>]"), std::string::npos)
        << "expected explicit type_name preserved verbatim in:\n"
        << out;
    EXPECT_EQ(out.find("--ring <RING>"), std::string::npos)
        << "must not override an explicit type_name with the derived "
           "placeholder in:\n"
        << out;
}

TEST(HelpFormatter, positional_arguments_render_in_arguments_section)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);
    std::string path;
    app.add_option("path", path, "input path");

    auto const out = render_help(app);
    EXPECT_NE(
        out.find("Usage: monad-test [OPTIONS] <ARGS>..."), std::string::npos)
        << out;
    EXPECT_NE(out.find("Arguments:"), std::string::npos)
        << "expected an Arguments: section for positional options in:\n"
        << out;
    EXPECT_NE(out.find("<PATH>"), std::string::npos)
        << "positional placeholder should render under Arguments:\n"
        << out;
    EXPECT_NE(out.find("input path"), std::string::npos);
}

TEST(HelpFormatter, snake_case_aliases_are_collapsed_to_first_long_name)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);
    std::string s;
    // The first listed long name is the one shown; the alias is consumed by
    // CLI11 for parsing but suppressed in the help layout.
    app.add_option("--block-db,--block_db", s, "block_db dir");

    auto const out = render_help(app);
    EXPECT_NE(out.find("--block-db"), std::string::npos) << out;
    EXPECT_EQ(out.find("--block_db"), std::string::npos)
        << "snake_case alias must not appear in --help in:\n"
        << out;
}

TEST(HelpFormatter, no_version_flag_is_installed)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);

    auto const out = render_help(app);
    EXPECT_EQ(out.find("--version"), std::string::npos)
        << "install() must not install a --version flag in:\n"
        << out;
    EXPECT_EQ(out.find("Print version"), std::string::npos);
}

TEST(HelpFormatter, option_group_options_appear_in_flat_options_section)
{
    CLI::App app{"desc", "monad-test"};
    HelpFormatter{"v0"}.install(app);
    auto *group = app.add_option_group("mode", "mode group");
    bool interactive = false;
    group->add_flag("--interactive", interactive, "set interactive mode");

    auto const out = render_help(app);
    EXPECT_NE(out.find("Options:"), std::string::npos) << out;
    EXPECT_NE(out.find("--interactive"), std::string::npos)
        << "options added via add_option_group must surface in the flat "
           "Options: block:\n"
        << out;
    EXPECT_EQ(out.find("Commands:"), std::string::npos)
        << "option_groups must not surface as user-facing Commands in:\n"
        << out;
}
