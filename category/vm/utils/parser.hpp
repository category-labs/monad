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
     *
     */
    std::vector<uint8_t>
    parse_opcodes(parser_config const &config, std::string const &str);

    /**
     *  convert from binary evm bytecode to text opcodes and data
     */
    std::string show_opcodes(std::vector<uint8_t> const &opcodes);

}
