#pragma once

#include <category/vm/core/assert.h>

#include <memory>
#include <utility>

namespace monad::vm::utils
{
    template <typename T>
    struct RcObject
    {
        size_t ref_count;
        T object;

        static RcObject<T> *default_allocate()
        {
            return std::allocator<RcObject<T>>().allocate(1);
        }

        static void default_deallocate(RcObject<T> *rco)
        {
            std::allocator<RcObject<T>>().deallocate(rco, 1);
        }

        struct DefaultDeleter
        {
            static void destroy(RcObject<T> *)
            {
                // nop
            }

            static void deallocate(RcObject<T> *rco)
            {
                default_deallocate(rco);
            }
        };
    };

    template <typename T, typename Deleter>
    class RcPtr
    {
    public:
        template <typename Allocator, typename... Args>
        static RcPtr make(Allocator const &allocate, Args &&...args)
        {
            RcPtr p{allocate()};
            p.rc_object->ref_count = 1;
            new (&p.rc_object->object) T(std::forward<Args>(args)...);
            return p;
        }

        RcPtr()
            : rc_object{nullptr}
        {
        }

        RcPtr(RcPtr const &x)
            : rc_object{x.rc_object}
        {
            if (x.rc_object) {
                ++x.rc_object->ref_count;
            }
        }

        RcPtr(RcPtr &&x) noexcept
            : rc_object{x.rc_object}
        {
            x.rc_object = nullptr;
        }

        RcPtr &operator=(RcPtr const &x)
        {
            if (x.rc_object) {
                ++x.rc_object->ref_count;
            }
            release();
            rc_object = x.rc_object;
            return *this;
        }

        RcPtr &operator=(RcPtr &&x) noexcept
        {
            release();
            rc_object = x.rc_object;
            x.rc_object = nullptr;
            return *this;
        }

        void reset()
        {
            release();
            rc_object = nullptr;
        }

        RcPtr &operator=(std::nullptr_t)
        {
            reset();
            return *this;
        }

        ~RcPtr()
        {
            release();
        }

        void swap(RcPtr &x) noexcept
        {
            std::swap(rc_object, x.rc_object);
        }

        T &operator*() const
        {
            return rc_object->object;
        }

        T *operator->() const
        {
            return &rc_object->object;
        }

        friend bool operator==(RcPtr const &x, RcPtr const &y)
        {
            return x.rc_object == y.rc_object;
        }

        // Note: undefined when RcPtr is nullptr.
        T *get() const
        {
            MONAD_VM_DEBUG_ASSERT(rc_object != nullptr);
            return &rc_object->object;
        }

        explicit operator bool() const
        {
            return rc_object;
        }

    private:
        explicit RcPtr(RcObject<T> *rco)
            : rc_object{rco}
        {
        }

        void release()
        {
            if (rc_object && !--rc_object->ref_count) {
                Deleter::destroy(rc_object);
                rc_object->object.~T();
                Deleter::deallocate(rc_object);
            }
        }

        RcObject<T> *rc_object;
    };
}

namespace std
{
    template <typename T, typename Deleter>
    void swap(
        monad::vm::utils::RcPtr<T, Deleter> &x,
        monad::vm::utils::RcPtr<T, Deleter> &y) noexcept
    {
        x.swap(y);
    }
}
