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

#include <ankerl/unordered_dense.h>

MONAD_NAMESPACE_BEGIN

/* std::unordered_map is very slow by modern hash table standards (see
  https://martin.ankerl.com/2022/08/27/hashmap-bench-01/#random-insert--access-uint64_t),
  so use a much better third party map implementation.

  I've chosen ankerl's hash maps, even though he's almost certainly biased in
  his benchmarking. I think his hash maps won't be especially slower than
  alternatives, and he makes single include file self contained implementations
  which makes them very easy to integrate. They don't splosh outside their
  namespaces, and don't interfere with other code.

  His hash maps are virtually unusable in the debugger, so if `NDEBUG` is not
  defined, everything turns into `std::unordered_map`.

  Here are some sample not representative comparative benchmarks:

   Testing std::unordered_set with 16 byte values ... 4.20588
   Testing unordered_node_set with 16 byte values ... 1.71718
   Testing unordered_dense_set with 16 byte values ... 1.62627
   Testing unordered_flat_set with 16 byte values ... 1.54331

   Testing std::unordered_set with 64 byte values ... 12.4591
   Testing unordered_node_set with 64 byte values ... 5.70922
   Testing unordered_dense_set with 64 byte values ... 5.39463
   Testing unordered_flat_set with 64 byte values ... 7.09919

   Testing std::unordered_set with 256 byte values ... 15.3815
   Testing unordered_node_set with 256 byte values ... 7.54056
   Testing unordered_dense_set with 256 byte values ... 7.45862
   Testing unordered_flat_set with 256 byte values ... 10.9794

   Testing std::unordered_set with 512 byte values ... 18.2916
   Testing unordered_node_set with 512 byte values ... 9.40263
   Testing unordered_dense_set with 512 byte values ... 9.91596
   Testing unordered_flat_set with 512 byte values ... 14.1972


  This is why we have metaprogramming cut off values past a certain size.
*/

namespace detail
{
    class unordered_dense_map_disabled;
    class unordered_dense_set_disabled;
} // namespace detail

/*! \brief A much faster inline-storage-based alternative to
`std::unordered_map`, usually around 5x faster.

- This is NOT drop in compatible with `std::unordered_map` as references are not
stable to modification.
- State of the art insertion and lookup speed but at the cost of removal speed.
If you need fast removals, use `unordered_flat_map` instead.
- Supports PMR custom allocators and the C++ 17 map extraction extensions.
- Metaprogramming disables implementation with a useful compiler diagnostic if
value type's size exceeds 384 bytes, as you probably should use a node map
instead for such large values.

Be aware:

- Maximum item count is 2^32-1.
*/
template <class Key, class T, class Hash = ankerl::unordered_dense::hash<Key>>
using unordered_dense_map = std::conditional_t<
    sizeof(std::pair<Key, T>) <= 384,
    ankerl::unordered_dense::segmented_map<Key, T, Hash>,
    detail::unordered_dense_map_disabled>;
template <class Key, class Hash = ankerl::unordered_dense::hash<Key>>
using unordered_dense_set = std::conditional_t<
    sizeof(Key) <= 384, ankerl::unordered_dense::segmented_set<Key, Hash>,
    detail::unordered_dense_set_disabled>;

MONAD_NAMESPACE_END
