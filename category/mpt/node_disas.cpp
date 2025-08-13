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

#include <category/mpt/node.hpp>

MONAD_MPT_NAMESPACE_BEGIN

uint16_t child_mask_disas(Node const &node)
{
    return child_mask(node);
}

bool child_test_disas(Node const &node, unsigned const i)
{
    return child_test(node, i);
}

bool child_all_disas(Node const &node)
{
    return child_all(node);
}

bool child_any_disas(Node const &node)
{
    return child_any(node);
}

bool child_none_disas(Node const &node)
{
    return child_none(node);
}

unsigned child_count_disas(Node const &node)
{
    return child_count(node);
}

unsigned child_index_disas(Node const &node, unsigned const i)
{
    return child_index(node, i);
}

std::pair<unsigned char const *, unsigned char>
child_path_disas(Node const &node, unsigned const i)
{
    return child_path(node, i);
}

MONAD_MPT_NAMESPACE_END
