#pragma once

#include <category/core/config.hpp>

#include <cstddef>
#include <new>
#include <utility>

MONAD_NAMESPACE_BEGIN

class HugeMem final
{
    size_t size_{0};
    unsigned char *data_{nullptr};

public:
    explicit HugeMem(size_t size);

    HugeMem() = default;

    HugeMem(HugeMem const &) = delete;

    HugeMem(HugeMem &&other) noexcept
        : size_(other.size_)
        , data_(other.data_)
    {
        other.size_ = 0;
        other.data_ = nullptr;
    }

    HugeMem &operator=(HugeMem const &) = delete;

    HugeMem &operator=(HugeMem &&other) noexcept
    {
        if (this != &other) {
            this->~HugeMem();
            new (this) HugeMem(std::move(other));
        }
        return *this;
    }

    ~HugeMem();

    [[gnu::always_inline]] size_t get_size() const
    {
        return size_;
    }

    [[gnu::always_inline]] unsigned char *get_data() const
    {
        return data_;
    }
};

static_assert(sizeof(HugeMem) == 16);
static_assert(alignof(HugeMem) == 8);

MONAD_NAMESPACE_END
