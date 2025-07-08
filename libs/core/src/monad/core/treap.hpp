#pragma once

#include <monad/config.hpp>
#include <monad/core/assert.h>

#include <quill/Quill.h>

MONAD_NAMESPACE_BEGIN

/*
   Class template for the treap data structure. Template parameter class 'Node'
   must have a member function 'priority'.
 */
template <class Node, Node *Node::*left_, Node *Node::*right_>
class Treap
{
    Node *root_{nullptr};

public:
    template <class Func>
    Node **find_lt(Func const lt)
    {
        return find_lt(root_, lt);
    }

    template <class Func>
    Node **find_gte(Func const gte)
    {
        return find_gte(root_, gte);
    }

    template <class Func>
    void insert(Node *const node, Func const lt)
    {
        insert(root_, node, lt);
    }

    template <class Func>
    void remove_exact(Node *const node, Func const lt)
    {
        remove_exact(root_, node, lt);
    }

    template <class Func>
    Node *remove_gte(Func const gte)
    {
        return remove_gte(root_, gte);
    }

    void print_preorder()
    {
        print_preorder(root_);
    }

private:
    template <class Func>
    Node **find_lt(Node *&root, Func const lt) const
    {
        Node **link = nullptr;
        if (root) {
            if (lt(root)) {
                link = &root;
                Node **const res = find_lt(root->*right_, lt);
                if (res) {
                    link = res;
                }
            }
            else {
                link = find_lt(root->*left_, lt);
            }
        }
        return link;
    }

    template <class Func>
    Node **find_gte(Node *&root, Func const gte) const
    {
        Node **link = nullptr;
        if (root) {
            if (gte(root)) {
                link = &root;
                Node **const res = find_gte(root->*left_, gte);
                if (res) {
                    link = res;
                }
            }
            else {
                link = find_gte(root->*right_, gte);
            }
        }
        return link;
    }

    template <class Func>
    Node **find_exact(Node *&root, Node *const node, Func const lt) const
    {
        MONAD_DEBUG_ASSERT(root);
        return root == node
                   ? &root
                   : find_exact(
                         lt(root) ? root->*right_ : root->*left_, node, lt);
    }

    template <class Func>
    void insert(Node *&root, Node *const node, Func const lt)
    {
        if (!root) {
            root = node;
        }
        else if (lt(node, root)) {
            MONAD_DEBUG_ASSERT(
                root->*left_ == nullptr || lt(root->*left_, root));
            insert(root->*left_, node, lt);
            if ((root->*left_)->priority() > root->priority()) {
                rotate_right(root);
            }
        }
        else {
            MONAD_DEBUG_ASSERT(
                root->*right_ == nullptr || lt(root, root->*right_));
            insert(root->*right_, node, lt);
            if ((root->*right_)->priority() > root->priority()) {
                rotate_left(root);
            }
        }
    }

    template <class Func>
    void remove_exact(Node *&root, Node *const node, Func const lt)
    {
        Node *&link = *find_exact(root, node, lt);
        link = merge(link->*left_, link->*right_);
        node->*left_ = node->*right_ = nullptr;
    }

    template <class Func>
    Node *remove_gte(Node *&root, Func const gte)
    {
        Node **link = find_gte(root, gte);
        if (!link) {
            return nullptr;
        }
        MONAD_DEBUG_ASSERT(link);
        Node *const node = *link;
        *link = merge(node->*left_, node->*right_);
        node->*left_ = node->*right_ = nullptr;
        return node;
    }

    Node *merge(Node *const l, Node *const r)
    {
        if (!l) {
            return r;
        }
        if (!r) {
            return l;
        }
        if (l->priority() > r->priority()) {
            l->*right_ = merge(l->*right_, r);
            return l;
        }
        else {
            r->*left_ = merge(l, r->*left_);
            return r;
        }
    }

    void rotate_left(Node *&root)
    {
        Node *const r = root->*right_;
        root->*right_ = r->*left_;
        r->*left_ = root;
        root = r;
    }

    void rotate_right(Node *&root)
    {
        Node *const l = root->*left_;
        root->*left_ = l->*right_;
        l->*right_ = root;
        root = l;
    }

    void print_preorder(Node *root) const
    {
        if (root) {
            LOG_INFO(
                "***   {} {:x} {} -- {} {}",
                (void *)root,
                root->size_,
                root->priority(),
                (void *)(root->*left_),
                (void *)(root->*right_));
            MONAD_DEBUG_ASSERT(root != root->*left_);
            MONAD_DEBUG_ASSERT(root != root->*right_);
            print_preorder(root->*left_);
            print_preorder(root->*right_);
        }
    }
};

MONAD_NAMESPACE_END
