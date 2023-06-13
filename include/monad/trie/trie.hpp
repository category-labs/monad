#pragma once

#include <monad/trie/key_buffer.hpp>
#include <monad/trie/nibbles.hpp>
#include <monad/trie/node.hpp>
#include <monad/trie/process_transformation_list.hpp>
#include <monad/trie/update.hpp>
#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/variant.hpp>

#include <tl/optional.hpp>

#include <algorithm>
#include <bit>
#include <iterator>
#include <variant>
#include <vector>

MONAD_TRIE_NAMESPACE_BEGIN

[[nodiscard]] constexpr Nibbles const &get_update_key(Update const &u)
{
    return std::visit(
        [](auto const &ud) -> Nibbles const & { return ud.key; }, u);
}

[[nodiscard]] constexpr bool is_deletion(Update const &u)
{
    return std::holds_alternative<Delete>(u);
}

[[nodiscard]] constexpr byte_string const &get_upsert_value(Update const &u)
{
    return std::get<Upsert>(u).value;
}

[[nodiscard]] constexpr bool
are_parents_same(Nibbles const &k1, Nibbles const &k2)
{
    assert(!(k1.empty() && k2.empty()));

    if (k1.empty() || k2.empty()) {
        return false;
    }

    return k1.prefix(k1.size() - 1) == k2.prefix(k2.size() - 1);
}

template <typename TCursor, typename TWriter>
struct Trie
{
    using trie_key_t = typename TCursor::Key;

    TCursor &leaves_cursor_;
    TCursor &trie_cursor_;
    TWriter &leaves_writer_;
    TWriter &trie_writer_;
    KeyBuffer buf_;

    using update_iterator_t = typename std::vector<Update>::const_iterator;
    using optional_iterator_t =
        std::variant<std::monostate, trie_key_t, update_iterator_t>;

    constexpr Trie(
        TCursor &leaves, TCursor &all, TWriter &leaves_writer,
        TWriter &trie_writer)
        : leaves_cursor_(leaves)
        , trie_cursor_(all)
        , leaves_writer_(leaves_writer)
        , trie_writer_(trie_writer)
    {
    }

    constexpr void clear()
    {
        leaves_writer_.del_prefix(buf_.prefix());
        trie_writer_.del_prefix(buf_.prefix());
    }

    constexpr void take_snapshot()
    {
        leaves_cursor_.take_snapshot();
        trie_cursor_.take_snapshot();
    }

    constexpr void set_trie_prefix(address_t const &prefix)
    {
        buf_.set_prefix(prefix);
        leaves_cursor_.set_prefix(prefix);
        trie_cursor_.set_prefix(prefix);
    }

    // Process updates and queue up writes to disk. returns root hash
    // of trie after updates are processed
    bytes32_t process_updates(std::vector<Update> const &updates)
    {
        // updates should come in sorted order
        assert(std::ranges::is_sorted(
            updates, std::ranges::less{}, get_update_key));

        assert(!updates.empty());

        // there should be no duplicate updates
        assert(
            std::ranges::adjacent_find(
                updates, std::equal_to<>{}, get_update_key) == updates.end());

        // all updates should be to leaves (approximate this by checking size)
        assert(std::ranges::all_of(
            updates,
            [&updates](auto const &s) {
                return s == get_update_key(updates.front()).size();
            },
            [](auto const &u) { return get_update_key(u).size(); }));

        auto list = [&]() -> std::list<Node> {
            if (leaves_cursor_.empty()) {
                std::list<Node> ret;
                std::ranges::transform(
                    updates, std::back_inserter(ret), [](auto const &update) {
                        assert(!is_deletion(update));
                        return Leaf{
                            get_update_key(update), get_upsert_value(update)};
                    });
                return ret;
            }
            return generate_transformation_list(updates);
        }();

        auto const finalize_and_emit = [&](LeafOrBranch auto &node,
                                           uint8_t key_size) {
            using DecayedNode = std::decay_t<decltype(node)>;

            // if the key is changing, delete the old one
            if (node.key_size && node.key_size != key_size) {
                serialize_nibbles(
                    buf_, node.path_to_node.prefix(*node.key_size));
                trie_writer_.del(buf_);
            }

            node.finalize(key_size);

            auto const value = serialize_node(node);

            serialize_nibbles(buf_, node.path_to_node.prefix(*node.key_size));
            trie_writer_.put(buf_, value);
            if constexpr (std::same_as<DecayedNode, Leaf>) {
                serialize_nibbles(buf_, node.path_to_node);
                leaves_writer_.put(buf_, {});
            }
        };

        return process_transformation_list_dead_simple(
            std::move(list), finalize_and_emit);
    }

    [[nodiscard]] std::list<Node>
    generate_transformation_list(std::vector<Update> const &updates)
    {
        assert(!updates.empty());

        // pre-process
        std::vector<Nibbles> trie_keys;
        trie_keys.reserve(updates.size());

        for (auto it = updates.begin(); it < updates.end(); ++it) {
            trie_keys.push_back(get_key(it));
            if (is_deletion(*it)) {
                // TODO: to optimize this, only delete nodes that we know
                // exist and need to be deleted. Look at perf to see if we
                // bottleneck here
                // if this becomes a bottle neck, search for the
                // key first and then delete starting from there.
                // This will initiate less delete calls

                serialize_nibbles(buf_, get_update_key(*it));
                leaves_writer_.del(buf_);

                while (!buf_.path_empty()) {
                    trie_writer_.del(buf_);
                    buf_.path_pop_back();
                }

                // and make sure to delete the root too
                trie_writer_.del(buf_);
            }
        }

        std::list<Node> ret;
        bool found = move_to_previous(updates.begin(), trie_keys.at(0));

        while (found) {
            MONAD_ASSERT(trie_cursor_.valid());

            // TODO: push back and then reverse for more optimized
            ret.insert(
                ret.begin(),
                deserialize_node(
                    trie_cursor_.key()->path(), *trie_cursor_.value()));
            found = move_to_previous();
            MONAD_ASSERT(trie_cursor_.valid());
        }

        NextResult result = FromUpdate{
            .it = updates.begin(), .next_update = std::next(updates.begin())};

        if (is_deletion(*updates.begin())) {
            assert(std::holds_alternative<FromUpdate>(result));
            result = next(std::get<FromUpdate>(result), updates, trie_keys);
        }

        while (!std::holds_alternative<None>(result)) {
            std::visit(
                overloaded{
                    [](None) { assert(false); },
                    [&](FromUpdate from) {
                        assert(from.it != updates.end());
                        assert(!is_deletion(*from.it));

                        ret.push_back(Leaf{
                            get_update_key(*from.it),
                            get_upsert_value(*from.it)});
                        result = next(from, updates, trie_keys);
                    },
                    [&](FromStorage from) {
                        MONAD_ASSERT(trie_cursor_.valid());

                        ret.push_back(deserialize_node(
                            trie_cursor_.key()->path(), *trie_cursor_.value()));

                        result = next(from, updates, trie_keys);
                        MONAD_ASSERT(trie_cursor_.valid());
                    }},
                result);
        }

        return ret;
    }

    [[nodiscard]] constexpr bytes32_t root_hash() const
    {
        if (leaves_cursor_.empty()) {
            return NULL_ROOT;
        }
        trie_cursor_.lower_bound({});
        MONAD_ASSERT(trie_cursor_.valid());
        return get_root_hash(deserialize_node(
            trie_cursor_.key()->path(), *trie_cursor_.value()));
    }

    [[nodiscard]] constexpr bool at_root() const
    {
        MONAD_ASSERT(trie_cursor_.valid());
        return trie_cursor_.key()->path_empty();
    }

    // Move the trie cursor to the node with the longest prefix
    //
    // Pre-condition: None
    // Post-condition: trie cursor points to entry with longest prefix
    constexpr void move_to_longest_prefix(
        Nibbles const &start, tl::optional<trie_key_t> const &last) const
    {
        assert(!start.empty());
        MONAD_ASSERT(!trie_cursor_.empty());

        auto current = start;
        current.pop_back();
        trie_cursor_.lower_bound(current, tl::nullopt, last);
        auto key = trie_cursor_.key();

        while (!key || key->path() != current) {
            assert(!current.empty());

            current.pop_back();
            trie_cursor_.lower_bound(current, tl::nullopt, key);
            key = trie_cursor_.key();
        }

        assert(key && key->path() != start && start.startswith(key->path()));
    }

    constexpr void move_to_parent()
    {
        assert(!at_root());
        MONAD_ASSERT(trie_cursor_.valid());

        auto const curr = trie_cursor_.key();
        auto const curr_path = curr->path();
        move_to_longest_prefix(curr_path, curr);

        MONAD_ASSERT(trie_cursor_.valid());

        auto const parent =
            deserialize_node(trie_cursor_.key()->path(), *trie_cursor_.value());
        auto const parent_path = std::visit(&BaseNode::path_to_node, parent);

        assert(std::holds_alternative<Branch>(parent));
        assert(parent_path == curr_path.prefix(curr_path.size() - 1));
    }

    // return the key that the update would have if inserted into storage
    // in isolation
    [[nodiscard]] constexpr Nibbles get_key(update_iterator_t update)
    {
        assert(!leaves_cursor_.empty());

        leaves_cursor_.lower_bound(get_update_key(*update));
        auto const lb = leaves_cursor_.key();

        leaves_cursor_.prev();
        auto const prev = leaves_cursor_.key();

        auto const left = leaves_cursor_.key().and_then(
            [&](auto const &prev) -> tl::optional<uint8_t> {
                return longest_common_prefix_size(
                    prev.path(), get_update_key(*update));
            });

        auto const right =
            lb.and_then([&](auto const &lb) -> tl::optional<uint8_t> {
                if (lb.path() == get_update_key(*update)) {
                    leaves_cursor_.next();
                    MONAD_ASSERT(leaves_cursor_.key() == lb);

                    leaves_cursor_.next();

                    return leaves_cursor_.key().and_then(
                        [&](auto const &next) -> tl::optional<uint8_t> {
                            return longest_common_prefix_size(
                                next.path(), get_update_key(*update));
                        });
                }
                return longest_common_prefix_size(
                    lb.path(), get_update_key(*update));
            });

        // Nothing to the left or right, we are updating the only
        // leaf in the trie
        if (!left && !right) {
            return Nibbles{};
        }

        // key is parent path + branch (prefix of trie is invisible here)
        return Nibbles{get_update_key(*update).prefix(
            std::max(left.value_or(0), right.value_or(0)) + 1)};
    }

    // returns whether or not there is a previous
    // if true, cursor will point at the prev element
    [[nodiscard]] constexpr bool
    move_to_previous(update_iterator_t from, Nibbles const &trie_key)
    {
        assert(!leaves_cursor_.empty());

        trie_cursor_.lower_bound(trie_key);
        auto const lb = trie_cursor_.key();
        auto const lb_path = lb.map(&trie_key_t::path);

        // node exists
        if (lb_path && std::visit(
                           &BaseNode::path_to_node,
                           deserialize_node(*lb_path, *trie_cursor_.value())) ==
                           get_update_key(*from)) {
            return move_to_previous();
        }

        trie_cursor_.prev();

        auto const prev = trie_cursor_.key().map(&trie_key_t::path);
        MONAD_ASSERT(prev);

        // node does not exist, but parent exists
        if (are_parents_same(*prev, trie_key) ||
            (lb_path && are_parents_same(*lb_path, trie_key))) {
            // insertion at end of branch
            if (!lb_path || !are_parents_same(*lb_path, trie_key)) {
                move_to_parent();
                return true;
            }
            trie_cursor_.next();
            MONAD_ASSERT(trie_cursor_.key().map(&trie_key_t::path) == lb_path);
            return move_to_previous();
        }

        // node does not exist, and parent does not exist
        move_to_longest_prefix(trie_key, lb);

        MONAD_ASSERT(trie_cursor_.valid());

        if (std::visit(
                &BaseNode::path_to_node,
                deserialize_node(
                    trie_cursor_.key()->path(), *trie_cursor_.value())) <
            trie_key) {
            return true;
        }

        return move_to_previous();
    }

    [[nodiscard]] constexpr bool move_to_previous()
    {
        // base cases for the root
        if (at_root()) {
            return false;
        }

        auto const curr = trie_cursor_.key().map(&trie_key_t::path);
        MONAD_ASSERT(curr);
        trie_cursor_.prev();
        auto const prev = trie_cursor_.key().map(&trie_key_t::path);
        MONAD_ASSERT(prev);

        // first sibling in branch
        if (!are_parents_same(*prev, *curr)) {
            trie_cursor_.next();
            MONAD_ASSERT(trie_cursor_.key().map(&trie_key_t::path) == curr);
            move_to_parent();
            return move_to_previous();
        }

        return true;
    }

    struct None
    {
    };
    struct FromStorage
    {
        update_iterator_t next_update;
    };
    struct FromUpdate
    {
        update_iterator_t it;
        update_iterator_t next_update;
    };
    using NextResult = std::variant<None, FromStorage, FromUpdate>;

    template <typename T>
        requires std::same_as<T, FromStorage> || std::same_as<T, FromUpdate>
    [[nodiscard]] constexpr NextResult next(
        T const &from, std::vector<Update> const &updates,
        std::vector<Nibbles> const &trie_keys)
    {
        bool const from_storage = [&]() {
            // Move cursor to next in storage
            if constexpr (std::same_as<T, FromStorage>) {
                return move_to_next();
            }
            else {
                assert(from.it >= updates.begin());
                return move_to_next(
                    from.it,
                    trie_keys.at(
                        size_t(std::distance(updates.begin(), from.it))));
            }
        }();

        auto const next_update = from.next_update;

        // nothing from storage
        if (!from_storage) {
            if (next_update == updates.end()) {
                return None{};
            }

            assert(!is_deletion(*next_update));

            return FromUpdate{
                .it = next_update, .next_update = std::next(next_update)};
        }

        MONAD_ASSERT(trie_cursor_.valid());

        // no more updates to consider
        if (next_update == updates.end()) {
            return FromStorage{.next_update = updates.end()};
        }

        assert(next_update > updates.begin());
        auto const update_key =
            trie_keys.at(size_t(std::distance(updates.begin(), next_update)));

        // Update is to the root
        if (update_key.empty()) {
            MONAD_ASSERT(trie_cursor_.key()->path().empty());
            return FromUpdate{
                .it = next_update, .next_update = std::next(next_update)};
        }

        auto const update_parent_path =
            update_key.prefix(update_key.size() - 1);
        auto node =
            deserialize_node(trie_cursor_.key()->path(), *trie_cursor_.value());

        // Find highest root that is not dirtied by the next update
        while (std::holds_alternative<Branch>(node) &&
               get_update_key(*next_update)
                   .startswith(std::get<Branch>(node).path_to_node)) {

            auto const &branch = std::get<Branch>(node);

            // next update is insert at end of branch, return the branch itself
            if (update_parent_path == branch.path_to_node &&
                !is_deletion(*next_update) &&
                branch.last_branch() <
                    get_update_key(*next_update)[update_parent_path.size()]) {
                return FromStorage{.next_update = next_update};
            }

            auto const curr = trie_cursor_.key();
            MONAD_ASSERT(curr);
            trie_cursor_.lower_bound(branch.first_child(), curr);
            MONAD_ASSERT(trie_cursor_.valid());
            node = deserialize_node(
                trie_cursor_.key()->path(), *trie_cursor_.value());
        }

        if (std::visit(&BaseNode::path_to_node, node) <
            get_update_key(*next_update)) {
            return FromStorage{.next_update = next_update};
        }

        if (is_deletion(*next_update)) {
            return next(
                FromUpdate{
                    .it = next_update, .next_update = std::next(next_update)},
                updates,
                trie_keys);
        }

        return FromUpdate{
            .it = next_update, .next_update = std::next(next_update)};
    }

    [[nodiscard]] constexpr bool move_to_next()
    {
        if (MONAD_UNLIKELY(at_root())) {
            return false;
        }

        auto const from_path = trie_cursor_.key()->path();
        trie_cursor_.next();
        auto const next = trie_cursor_.key().map(&trie_key_t::path);

        // last sibling
        if (!next || !are_parents_same(from_path, *next)) {
            trie_cursor_.prev();
            MONAD_ASSERT(
                trie_cursor_.key().map(&trie_key_t::path) == from_path);
            move_to_parent();
            return move_to_next();
        }

        return true;
    }

    [[nodiscard]] constexpr bool
    move_to_next(update_iterator_t update, Nibbles const &key)
    {
        assert(!leaves_cursor_.empty());

        trie_cursor_.lower_bound(key);
        auto const lb = trie_cursor_.key();
        auto const lb_path = lb.map(&trie_key_t::path);
        auto const lb_value = trie_cursor_.value();

        // TODO: see if can get rid of all these path_to_node calls
        // now that the key is guaranteed to be unique
        //
        // node exists
        if (lb_path && std::visit(
                           &BaseNode::path_to_node,
                           deserialize_node(*lb_path, *trie_cursor_.value())) ==
                           get_update_key(*update)) {
            return move_to_next();
        }

        assert(!is_deletion(*update));

        // if key is empty, then it is the root, which should not be
        // possible if reaching this point
        assert(!key.empty());

        trie_cursor_.prev();
        auto const prev = trie_cursor_.key().map(&trie_key_t::path);
        MONAD_ASSERT(prev);

        // node does not exist, but parent exists
        if (are_parents_same(*prev, key) ||
            (lb_path && are_parents_same(*lb_path, key))) {
            // insertion at end of branch
            if (!lb_path || !are_parents_same(*lb_path, key)) {
                move_to_parent();
                return move_to_next();
            }
            trie_cursor_.next();
            MONAD_ASSERT(trie_cursor_.key().map(&trie_key_t::path) == lb_path);
            return true;
        }

        // node does not exist, and parent does not exist
        move_to_longest_prefix(key, lb);

        MONAD_ASSERT(trie_cursor_.valid());

        if (key < std::visit(
                      &BaseNode::path_to_node,
                      deserialize_node(
                          trie_cursor_.key()->path(), *trie_cursor_.value()))) {
            return true;
        }

        return move_to_next();
    }
};

MONAD_TRIE_NAMESPACE_END
