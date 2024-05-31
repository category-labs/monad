#pragma once

#include <monad/config.hpp>

#include <cstddef>
#include <new>

MONAD_NAMESPACE_BEGIN

class MemMap final
{
    size_t size_{0};
    unsigned char *data_{nullptr};

public:
    MemMap() = default;
    explicit MemMap(size_t size, size_t pagesize = 0);
    ~MemMap();

    MemMap(MemMap &&other) noexcept
        : size_(other.size_)
        , data_(other.data_)
    {
        other.size_ = 0;
        other.data_ = nullptr;
    }

    MemMap(MemMap const &) = delete;

    MemMap &operator=(MemMap &&other) noexcept
    {
        if (this != &other) {
            this->~MemMap();
            new (this) MemMap(static_cast<MemMap &&>(other));
        }
        return *this;
    }

    MemMap &operator=(MemMap const &) = delete;

    [[gnu::always_inline]] size_t get_size() const
    {
        return size_;
    }

    [[gnu::always_inline]] unsigned char *get_data() const
    {
        return data_;
    }
};

static_assert(sizeof(MemMap) == 16);
static_assert(alignof(MemMap) == 8);

MONAD_NAMESPACE_END
