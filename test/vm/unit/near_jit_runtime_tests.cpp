// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/vm/compiler/ir/x86/near_jit_runtime.hpp>

#include <asmjit/x86.h>

#include <gtest/gtest.h>

#include <sys/resource.h>

#include <cstddef>
#include <cstdint>
#include <vector>

using namespace monad::vm::compiler::native;

namespace
{
    using Fn = int (*)();

    int forty_two()
    {
        return 42;
    }

    Fn add_call(asmjit::JitRuntime &rt, size_t const padding = 0)
    {
        asmjit::CodeHolder code;
        code.init(rt.environment(), rt.cpuFeatures());
        asmjit::x86::Assembler as{&code};
        as.sub(asmjit::x86::rsp, 8);
        as.call(asmjit::imm(forty_two));
        as.add(asmjit::x86::rsp, 8);
        as.ret();
        for (size_t i = 0; i < padding; ++i) {
            as.int3();
        }
        Fn fn = nullptr;
        EXPECT_EQ(rt.add(&fn, &code), asmjit::kErrorOk);
        EXPECT_EQ(fn(), 42);
        return fn;
    }

    // The call follows the 4 byte `sub rsp, 8`.
    bool is_direct_call(Fn const fn)
    {
        auto const *const p = reinterpret_cast<uint8_t const *>(fn);
        return p[4] == 0x40 && p[5] == 0xE8;
    }
}

TEST(NearJitRuntime, DirectCall)
{
    // A runtime that never adds code must not take the near range.
    NearJitRuntime const idle{nullptr, size_t{1} << 30, 1};
    NearJitRuntime rt{nullptr, size_t{1} << 30, 1};
    auto const fn = add_call(rt);
    EXPECT_TRUE(is_direct_call(fn));
    rt.release(fn);
}

TEST(NearJitRuntime, FewCallSitesStayFar)
{
    NearJitRuntime rt{nullptr, size_t{1} << 30, 2};
    auto const fn = add_call(rt);
    EXPECT_FALSE(is_direct_call(fn));
    rt.release(fn);
}

TEST(NearJitRuntime, FileSizeLimit)
{
    rlimit old;
    ASSERT_EQ(getrlimit(RLIMIT_FSIZE, &old), 0);
    rlimit low = old;
    low.rlim_cur = 1 << 20;
    ASSERT_EQ(setrlimit(RLIMIT_FSIZE, &low), 0);
    {
        NearJitRuntime rt{nullptr, size_t{1} << 30, 1};
        auto const fn = add_call(rt);
        EXPECT_FALSE(is_direct_call(fn));
        rt.release(fn);
    }
    ASSERT_EQ(setrlimit(RLIMIT_FSIZE, &old), 0);
}

TEST(NearJitRuntime, FallbackAndReuse)
{
    NearJitRuntime rt{nullptr, 4096, 1};
    std::vector<Fn> near;
    for (size_t i = 0; i < 4096 / 64 - 1; ++i) {
        near.push_back(add_call(rt));
        EXPECT_TRUE(is_direct_call(near.back()));
    }
    auto const far = add_call(rt);
    EXPECT_FALSE(is_direct_call(far));
    for (auto const fn : near) {
        rt.release(fn);
    }
    auto const big = add_call(rt, 3900);
    EXPECT_TRUE(is_direct_call(big));
    rt.release(big);
    rt.release(far);
}
