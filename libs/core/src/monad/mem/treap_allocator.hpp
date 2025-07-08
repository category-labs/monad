#pragma once

#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/treap.hpp>
#include <monad/synchronization/spin_lock.hpp>

#include <mutex>

MONAD_NAMESPACE_BEGIN

class TreapAllocator
{
    // Minimum block size is sizeof(Node).

    struct Node
    {
        size_t size_;
        uint64_t const priority_;
        Node *a_left_{nullptr};
        Node *a_right_{nullptr};
        Node *s_left_{nullptr};
        Node *s_right_{nullptr};

        Node(size_t const size)
            : size_(size)
            , priority_(static_cast<uint64_t>(rand()))
        {
        }

        uint64_t priority() const
        {
            return priority_;
        }
    };

    SpinLock lock_;
    size_t avail_size_; // for debugging
    Treap<Node, &Node::a_left_, &Node::a_right_> addr_treap_;
    Treap<Node, &Node::s_left_, &Node::s_right_> size_treap_;

public:
    TreapAllocator(size_t const size, void *const ptr)
        : avail_size_(size)
    {
        Node *const node = new (ptr) Node(size);
        insert_in_treaps(node);
    }

    void *alloc(size_t const size)
    {
        MONAD_DEBUG_ASSERT(size >= sizeof(Node));
        void *ptr = nullptr;
        std::unique_lock g(lock_);
        Node *const node = remove_gte_from_size_treap(size);
        if (node) {
            remove_node_from_addr_treap(node);
            size_t const node_size = node->size_;
            MONAD_DEBUG_ASSERT(size <= node_size);
            ptr = static_cast<void *>(node);
            node->~Node();
            if (size < node_size) {
                void *const remain = static_cast<char *>(ptr) + size;
                Node *const node2 = new (remain) Node(node_size - size);
                insert_in_treaps(node2);
            }
            avail_size_ -= size;
        }
        MONAD_DEBUG_ASSERT(ptr);
        return ptr;
    }

    void dealloc(void *const ptr, size_t const size)
    {
        MONAD_DEBUG_ASSERT(size >= sizeof(Node));
        Node *const node = new (ptr) Node(size);
        std::unique_lock g(lock_);
        Node **const link1 = find_lt_in_addr_treap(node);
        Node *const node1 = link1 ? *link1 : nullptr;
        bool const cont1 =
            node1 && (static_cast<char *>(static_cast<void *>(node1)) +
                      node1->size_) == ptr;
        Node **const link2 = find_gt_in_addr_treap(node);
        Node *const node2 = link2 ? *link2 : nullptr;
        bool const cont2 = node2 && static_cast<char *>(ptr) + size ==
                                        static_cast<void *>(node2);
        if (cont2) {
            remove_node_from_addr_treap(node2);
            remove_node_from_size_treap(node2);
            node->size_ += node2->size_;
            node2->~Node();
        }
        if (cont1) {
            remove_node_from_size_treap(node1);
            node1->size_ += node->size_;
            node->~Node();
            insert_in_size_treap(node1);
        }
        else {
            insert_in_treaps(node);
        }
    }

private:
    void insert_in_treaps(Node *const node)
    {
        insert_in_addr_treap(node);
        insert_in_size_treap(node);
    }

    void insert_in_addr_treap(Node *const node)
    {
        auto const lt = [](Node *const node1, Node *const node2) {
            MONAD_DEBUG_ASSERT(node1 != node2);
            return node1 < node2;
        };
        addr_treap_.insert(node, lt);
    }

    void insert_in_size_treap(Node *const node)
    {
        auto const lt = [](Node *const node1, Node *const node2) {
            MONAD_DEBUG_ASSERT(node1 != node2);
            return (node1->size_ < node2->size_) ||
                   ((node1->size_ == node2->size_) && (node1 < node2));
        };
        size_treap_.insert(node, lt);
    }

    void remove_node_from_addr_treap(Node *const node)
    {
        auto const lt = [node](Node *const node2) {
            MONAD_DEBUG_ASSERT(node != node2);
            return node2 < node;
        };
        addr_treap_.remove_exact(node, lt);
    }

    void remove_node_from_size_treap(Node *const node)
    {
        auto const lt = [node](Node *const node2) {
            MONAD_DEBUG_ASSERT(node != node2);
            return (node2->size_ < node->size_) ||
                   ((node2->size_ == node->size_) && (node2 < node));
        };
        size_treap_.remove_exact(node, lt);
    }

    Node *remove_gte_from_size_treap(size_t const size)
    {
        auto const gte = [size](Node *const node) {
            return node->size_ >= size;
        };
        return size_treap_.remove_gte(gte);
    }

    Node **find_lt_in_addr_treap(Node *const node)
    {
        auto const lt = [node](Node *const node2) {
            MONAD_DEBUG_ASSERT(node != node2);
            return node2 < node;
        };
        return addr_treap_.find_lt(lt);
    }

    Node **find_gt_in_addr_treap(Node *const node)
    {
        auto const gt = [node](Node *const node2) {
            MONAD_DEBUG_ASSERT(node != node2);
            return node > node2;
        };
        return addr_treap_.find_gte(gt);
    }

    void print_treaps()
    {
        LOG_INFO("*** addr_treap");
        addr_treap_.print_preorder();
        LOG_INFO("*** size_treap");
        size_treap_.print_preorder();
    }
};

MONAD_NAMESPACE_END
