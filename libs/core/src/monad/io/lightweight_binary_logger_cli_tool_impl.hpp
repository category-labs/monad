#pragma once

#include <ostream>
#include <span>
#include <string_view>

#define MONAD_LBL_CLI_TOOL_DATETIME_FORMAT "%Y-%m-%dT%H:%M:%SZ"

extern int main_impl(
    std::ostream &cout, std::ostream &cerr, std::span<std::string_view> args);
