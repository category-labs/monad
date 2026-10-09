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

// Written by aotgen.py: the codes compiled ahead of time, by code hash.

#include <category/vm/aot/aot.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/types.hpp>

namespace monad::vm::aot
{
    namespace c_d0a06b12ac47863b
    {
        template <Traits traits>
        void run(
            void *, runtime::Context *, interpreter::Intercode const *,
            uint256_t *, void *);
    }

    namespace c_785f1014552b7ce7
    {
        template <Traits traits>
        void run(
            void *, runtime::Context *, interpreter::Intercode const *,
            uint256_t *, void *);
    }

    namespace c_cdfb7d322961af3a
    {
        template <Traits traits>
        void run(
            void *, runtime::Context *, interpreter::Intercode const *,
            uint256_t *, void *);
    }

    namespace c_5b83bdbcc56b2e63
    {
        template <Traits traits>
        void run(
            void *, runtime::Context *, interpreter::Intercode const *,
            uint256_t *, void *);
    }

    namespace c_b3bf58230b835d3e
    {
        template <Traits traits>
        void run(
            void *, runtime::Context *, interpreter::Intercode const *,
            uint256_t *, void *);
    }

    namespace c_b44fb4e949d0f78f
    {
        template <Traits traits>
        void run(
            void *, runtime::Context *, interpreter::Intercode const *,
            uint256_t *, void *);
    }

    namespace c_d80d4b7c890cb9d6
    {
        template <Traits traits>
        void run(
            void *, runtime::Context *, interpreter::Intercode const *,
            uint256_t *, void *);
    }

    using Osaka = EvmTraits<MONAD_ETH_OSAKA>;

    constexpr Entry entry_0{
        {0x3b8647ac126ba0d0u, 0xadea2d5c18e47b5cu, 0x7d6cf5337055611cu, 0x235eb2cb2944a74eu},
        3124,
        &c_d0a06b12ac47863b::run<Osaka>,
        nullptr};
    constexpr Entry entry_1{
        {0xe77c2b5514105f78u, 0xea60c970c7dfbd5u, 0xcad72504d04fe9deu, 0x9312cec7ca9a6021u},
        24009,
        &c_785f1014552b7ce7::run<Osaka>,
        nullptr};
    constexpr Entry entry_2{
        {0x3aaf6129327dfbcdu, 0xc2698beef7a8e7cau, 0x77b0c56c576fb305u, 0xeae3cb8eebc770f1u},
        23464,
        &c_cdfb7d322961af3a::run<Osaka>,
        nullptr};
    constexpr Entry entry_3{
        {0x632e6bc5bcbd835bu, 0xc2b0d2adbb07280fu, 0x582ab96680101916u, 0xe59c9e08611208deu},
        11293,
        &c_5b83bdbcc56b2e63::run<Osaka>,
        nullptr};
    constexpr Entry entry_4{
        {0x3e5d830b2358bfb3u, 0x6e843d0cc36ee413u, 0x16a9f78f9af2766u, 0x6cf263ab51b12a79u},
        6275,
        &c_b3bf58230b835d3e::run<Osaka>,
        nullptr};
    constexpr Entry entry_5{
        {0x8ff7d049e9b44fb4u, 0x3af22864e49ef787u, 0xbee0c66fce13572au, 0x55eac12a8ca7ddb3u},
        11075,
        &c_b44fb4e949d0f78f::run<Osaka>,
        nullptr};
    constexpr Entry entry_6{
        {0xd6b90c897c4b0dd8u, 0xb534bc526b3e89a4u, 0xe01637b15c33256bu, 0x515b4e68313d3d1u},
        2186,
        &c_d80d4b7c890cb9d6::run<Osaka>,
        nullptr};

    Entry const *const table[256] = {
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, &entry_3, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        &entry_1, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, &entry_4, &entry_5, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, &entry_2, nullptr, nullptr,
        &entry_0, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        &entry_6, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
        nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
    };
}
