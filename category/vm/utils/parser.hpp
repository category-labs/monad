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

#include <charconv>
#include <cstdint>
#include <iterator>
#include <span>
#include <stdexcept>
#include <string>
#include <system_error>
#include <vector>

namespace monad::vm::utils
{

    struct parser_config
    {
        // Whether to write info to stderr during parsing.
        bool const verbose;
        // Whether to validate the parsed program.
        bool const validate;
        // Reject ignored tokens and malformed labels; report errors by
        // exception.
        bool const strict = false;
    };

    /**
     * parse an evm opcode string and
     * return the resulting vector of evm bytecode
     *
     * Notes:
     * case is ignored
     * data can be in hex or decimal form
     * pushes can be statically sized (e.g. push3 0xabcdef)
     * or computed size (e.g. push 0xabcdef)
     * jumpdests can use named labels,
     * e.g. push .mylabel jumpdest .mylabel
     * end of line comments (// .. \n) and whitespace are ignored
     * source_lines, if provided, receives a source line number for each byte
     * strict mode throws std::invalid_argument on errors instead of exiting
     *
     */
    std::vector<uint8_t> parse_opcodes(
        parser_config const &config, std::string const &str,
        std::vector<uint32_t> *source_lines = nullptr);

    /**
     *  convert from binary evm bytecode to text opcodes and data
     */
    [[nodiscard]] std::string show_opcodes(std::vector<uint8_t> const &opcodes);

}
