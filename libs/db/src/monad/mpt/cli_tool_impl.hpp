#pragma once

#include <ostream>
#include <span>
#include <string_view>

extern int main_impl(
    std::ostream &cout, std::ostream &cerr, std::span<std::string_view> args);
