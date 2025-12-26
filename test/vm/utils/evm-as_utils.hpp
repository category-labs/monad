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

#include <category/vm/interpreter/execute.hpp>
#include <test/vm/utils/test_context.hpp>

namespace monad::vm::test
{
    class KernelCalldata
    {
    public:
        struct alignas(32) Point
        {
            uint8_t dims[32]{};
        };

        explicit KernelCalldata(size_t calldata_size)
            : data_(calldata_size >> 5){MONAD_VM_ASSERT(
                  (calldata_size & 31) == 0)}

            uint8_t
            & operator[](size_t i)
        {
            return data_[i >> 5].dims[i & 31];
        }

        uint8_t const &operator[](size_t i) const
        {
            return data_[i >> 5].dims[i & 31];
        }

        uint8_t *data()
        {
            return &(*this)[0];
        }

        uint8_t const *data() const
        {
            return &(*this)[0];
        }

        size_t size() const
        {
            return data_.size() << 5;
        }

    private:
        std::vector<Point> data_;
    };

    template <Traits traits>
    KernelCalldata to_throughput_calldata(
        size_t args_size, std::vector<uint8_t> const &base_calldata)
    {
        auto const max_stack_values =
            utils::evm_as::KernelBuilder<traits>::get_max_stack_values(
                args_size);

        auto const outer_step = max_stack_values * 32;
        auto const n = args_size == 0 ? 1 : args_size;

        MONAD_VM_ASSERT(base_calldata.size() % 32 == 0);
        MONAD_VM_ASSERT(base_calldata.size() >= outer_step);

        KernelCalldata ret(base_calldata.size());

        for (size_t count = 0, i = 0; i <= ret.size() - outer_step;
             i += outer_step) {
            for (size_t j = 0; j < max_stack_values; j += n) {
                for (size_t k = 0; k < n; ++k) {
                    size_t const c = i + 32 * (max_stack_values - j - n + k);
                    runtime::uint256_t::load_be_unsafe(
                        &base_calldata[count * 32])
                        .store_be(&ret[c]);
                    ++count;
                }
            }
        }

        return ret;
    }

    template <Traits traits>
    KernelCalldata to_latency_calldata(
        utils::evm_as::EvmBuilder<traits> seq, size_t args_size,
        KernelCalldata const &throughput_calldata)
    {
        using KB = utils::evm_as::KernelBuilder<traits>;

        KB kb;
        kb.latency_calldata(seq, args_size);

        std::vector<uint8_t> bytecode{};
        compile(kb, bytecode);

        interpreter::Intercode icode{bytecode};

        runtime::EvmStackAllocator stack_allocator;
        auto stack_memory = stack_allocator.allocate();
        TestContext ctx;
        ctx->gas_remaining = std::numeric_limits<int64_t>::max();
        ctx->env.input_data = throughput_calldata.data();
        ctx->env.input_data_size =
            static_cast<uint32_t>(throughput_calldata.size());

        interpreter::execute<traits>(*ctx, icode, stack_memory.get());

        size_t n = 32 * args_size *
                   KB::get_sequence_repetition_count(
                       args_size, throughput_calldata.size());
        MONAD_VM_ASSERT(ctx->result.status == runtime::StatusCode::Success);
        MONAD_VM_ASSERT(runtime::uint256_t::load_le(ctx->result.size) == n);
        MONAD_VM_ASSERT(runtime::uint256_t::load_le(ctx->result.offset) == 0);

        KernelCalldata ret{throughput_calldata.size()};
        std::memcpy(ret.data(), ctx->memory.data, n);
        return ret;
    }
}
