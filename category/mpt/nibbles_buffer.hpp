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

#pragma once

#include <category/core/assert.h>
#include <category/core/nibble.h>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <array>
#include <concepts>
#include <cstdint>
#include <cstring>

MONAD_MPT_NAMESPACE_BEGIN

// A nibble path of up to 255 nibbles held inline, for paths that are built
// and extended without a heap allocation.
class NibblesBuffer
{
    static constexpr unsigned max_nibbles = 255;

    std::array<unsigned char, 128> data_{};
    uint8_t size_{0}; // invariant: every nibble at or past size_ is zero

public:
    NibblesBuffer() = default;

    template <NibblesPiece... Args>
        requires(sizeof...(Args) > 0)
    explicit NibblesBuffer(Args const &...args)
    {
        (append_piece(args), ...);
    }

    void push_back(unsigned char const nibble)
    {
        MONAD_ASSERT(nibble <= 0xF);
        MONAD_ASSERT(size_ < max_nibbles);
        set_nibble(data_.data(), size_, nibble);
        ++size_;
    }

    void append(NibblesView const src)
    {
        MONAD_ASSERT(size_ + src.nibble_size() <= max_nibbles);
        copy_nibbles(data_.data(), size_, src);
        size_ = static_cast<uint8_t>(size_ + src.nibble_size());
    }

    void shrink(unsigned const new_size)
    {
        MONAD_ASSERT(new_size <= size_);
        if (new_size % 2 != 0) {
            data_[new_size / 2] &= 0xF0;
        }
        unsigned const keep_bytes = (new_size + 1) / 2;
        unsigned const used_bytes = (size_ + 1u) / 2;
        std::memset(data_.data() + keep_bytes, 0, used_bytes - keep_bytes);
        size_ = static_cast<uint8_t>(new_size);
    }

    unsigned nibble_size() const noexcept
    {
        return size_;
    }

    bool empty() const noexcept
    {
        return size_ == 0;
    }

    unsigned char get(unsigned const i) const
    {
        MONAD_ASSERT(i < size_);
        return get_nibble(data_.data(), i);
    }

    unsigned char const *data() const noexcept
    {
        return data_.data();
    }

    // NOLINTNEXTLINE(google-explicit-constructor)
    operator NibblesView() const noexcept
    {
        return NibblesView{0, size_, data_.data()};
    }

private:
    template <NibblesPiece T>
    void append_piece(T const &piece)
    {
        if constexpr (std::same_as<T, unsigned char>) {
            push_back(piece);
        }
        else {
            append(NibblesView{piece});
        }
    }
};

static_assert(sizeof(NibblesBuffer) == 129);

MONAD_MPT_NAMESPACE_END
