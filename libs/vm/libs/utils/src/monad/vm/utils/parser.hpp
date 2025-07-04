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
