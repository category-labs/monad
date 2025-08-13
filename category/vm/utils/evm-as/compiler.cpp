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

#include <category/vm/utils/evm-as/compiler.hpp>

#include <array>
#include <cstddef>
#include <limits>
#include <ostream>
#include <sstream>
#include <string>
#include <vector>

namespace monad::vm::utils::evm_as::internal
{
    using namespace monad::vm::utils::evm_as;

    static std::array<char, 6> var_letters = {'X', 'Y', 'Z', 'A', 'B', 'C'};

    void emit_annotation(
        annot_context &ctx, size_t prefix_len, size_t desired_offset,
        std::ostream &os)
    {
        // Emit whitespace to align annotations
        do {
            os << " ";
        }
        while (++prefix_len < desired_offset);

        // Truncate stack for n > 8
        size_t n = ctx.vstack.size();
        if (n > 8) {
            n = 6;
        }

        os << "// [";
        for (size_t i = 0; i < n; i++) {
            os << ctx.vstack[ctx.vstack.size() - i - 1];
            if (i + 1 < n) {
                os << ", ";
            }
        }
        if (ctx.vstack.size() > 8) {
            os << ", ..., " << ctx.vstack[0];
        }
        os << "]";
    }

    std::string new_var(annot_context &ctx)
    {
        std::stringstream ss{};
        ss << var_letters[ctx.next_letter++];
        ctx.next_letter = ctx.next_letter % var_letters.size();

        constexpr size_t sz = std::numeric_limits<size_t>::digits10;
        char buffer[sz];
        size_t i = 0;

        if (ctx.next_subscript == 0) {
            buffer[i++] = '0';
        }
        else {
            size_t value = ctx.next_subscript;
            while (value > 0) {
                buffer[i++] = static_cast<char>('0' + (value % 10));
                value /= 10;
            }
        }

        for (size_t j = 0; j < i; j++) {
            ss << buffer[i - j - 1];
        }

        if (ctx.next_letter == 0) {
            ctx.next_subscript++;
        }

        return ss.str();
    }
}
